{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module book.15-univalence where

import book.14-propositional-truncation-solutions
open book.14-propositional-truncation-solutions public

--------------------------------------------------------------------------------

-- The univalence axiom

--------------------------------------------------------------------------------

-- Section 15.1 Equivalent forms of the univalence axiom

-- Definition 15.1.1

equiv-eq : {i : Level} {A : UU i} {B : UU i} → Id A B → A ≃ B
equiv-eq {A = A} refl = equiv-id A

UNIVALENCE : {i : Level} (A B : UU i) → UU (lsuc i)
UNIVALENCE A B = is-equiv (equiv-eq {A = A} {B = B})

-- Theorem 15.1.2

is-contr-total-equiv-UNIVALENCE : {i : Level} (A : UU i) →
  ((B : UU i) → UNIVALENCE A B) → is-contr (Σ (UU i) (λ X → A ≃ X))
is-contr-total-equiv-UNIVALENCE A UA =
  fundamental-theorem-id' A
    ( equiv-id A)
    ( λ B → equiv-eq {B = B})
    ( UA)

UNIVALENCE-is-contr-total-equiv : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → A ≃ X)) → (B : UU i) → UNIVALENCE A B
UNIVALENCE-is-contr-total-equiv A c =
  fundamental-theorem-id A
    ( equiv-id A)
    ( c)
    ( λ B → equiv-eq {B = B})

ev-id : {i j : Level} {A : UU i} (P : (B : UU i) → (A ≃ B) → UU j) →
  ((B : UU i) (e : A ≃ B) → P B e) → P A (equiv-id A)
ev-id {A = A} P f = f A (equiv-id A)

IND-EQUIV : {i j : Level} {A : UU i} → ((B : UU i) (e : A ≃ B) → UU j) → UU _
IND-EQUIV P = sec (ev-id P)

triangle-ev-id : {i j : Level} {A : UU i}
  (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) →
  (ev-pt (Σ (UU i) (λ X → A ≃ X)) (pair A (equiv-id A)) P)
  ~ ((ev-id (λ X e → P (pair X e))) ∘ (ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P}))
triangle-ev-id P f = refl

abstract
  IND-EQUIV-is-contr-total-equiv : {i j : Level} (A : UU i) →
    is-contr (Σ (UU i) (λ X → A ≃ X)) →
    (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) → IND-EQUIV (λ B e → P (pair B e))
  IND-EQUIV-is-contr-total-equiv {i} {j} A c P =
    section-comp
      ( ev-pt (Σ (UU i) (λ X → A ≃ X)) (pair A (equiv-id A)) P)
      ( ev-id (λ X e → P (pair X e)))
      ( ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P})
      ( triangle-ev-id P)
      ( pair ind-Σ refl-htpy)
      ( is-sing-is-contr (Σ (UU i) (λ X → A ≃ X))
        ( pair
          ( pair A (equiv-id A))
          ( λ t → 
            ( inv (contraction c (pair A (equiv-id A)))) ∙
            ( contraction c t)))
        ( P)
        ( pair A (equiv-id A)))

abstract
  is-contr-total-equiv-IND-EQUIV : {i : Level} (A : UU i) →
    ( {j : Level} (P : (Σ (UU i) (λ X → A ≃ X)) → UU j) →
      IND-EQUIV (λ B e → P (pair B e))) →
    is-contr (Σ (UU i) (λ X → A ≃ X))
  is-contr-total-equiv-IND-EQUIV {i} A ind =
    is-contr-is-sing
      ( Σ (UU i) (λ X → A ≃ X))
      ( pair A (equiv-id A))
      ( λ P → section-comp'
        ( ev-pt (Σ (UU i) (λ X → A ≃ X)) (pair A (equiv-id A)) P)
        ( ev-id (λ X e → P (pair X e)))
        ( ev-pair {A = UU i} {B = λ X → A ≃ X} {C = P})
        ( triangle-ev-id P)
        ( pair ind-Σ refl-htpy)
        ( ind P))

-- The univalence axiom

postulate univalence : {i : Level} (A B : UU i) → UNIVALENCE A B

eq-equiv : {i : Level} (A B : UU i) → (A ≃ B) → Id A B
eq-equiv A B = inv-is-equiv (univalence A B)

abstract
  is-contr-total-equiv : {i : Level} (A : UU i) →
    is-contr (Σ (UU i) (λ X → A ≃ X))
  is-contr-total-equiv A = is-contr-total-equiv-UNIVALENCE A (univalence A)

inv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} (e : A ≃ B) →
  Id (inv-equiv (inv-equiv e)) e
inv-inv-equiv (pair f (pair (pair g G) (pair h H))) = eq-htpy-equiv refl-htpy

is-equiv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → is-equiv (inv-equiv {A = A} {B = B})
is-equiv-inv-equiv =
  is-equiv-has-inverse
    ( inv-equiv)
    ( inv-inv-equiv)
    ( inv-inv-equiv)

equiv-inv-equiv :
  {i j : Level} {A : UU i} {B : UU j} → (A ≃ B) ≃ (B ≃ A)
equiv-inv-equiv = pair inv-equiv is-equiv-inv-equiv

is-contr-total-equiv' : {i : Level} (A : UU i) →
  is-contr (Σ (UU i) (λ X → X ≃ A))
is-contr-total-equiv' A =
  is-contr-equiv
    ( Σ (UU _) (λ X → A ≃ X))
    ( equiv-tot (λ X → equiv-inv-equiv))
    ( is-contr-total-equiv A)

abstract
  Ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
    sec (ev-id P)
  Ind-equiv A P =
    IND-EQUIV-is-contr-total-equiv A
    ( is-contr-total-equiv A)
    ( λ t → P (pr1 t) (pr2 t))

ind-equiv : {i j : Level} (A : UU i) (P : (B : UU i) (e : A ≃ B) → UU j) →
  P A (equiv-id A) → {B : UU i} (e : A ≃ B) → P B e
ind-equiv A P p {B} = pr1 (Ind-equiv A P) p B

--------------------------------------------------------------------------------

-- Section 15.2 Univalence implies function extensionality

-- Lemma 15.2.1

is-equiv-postcomp-univalence :
  {l1 l2 : Level} {X Y : UU l1} (A : UU l2) (e : X ≃ Y) →
  is-equiv (postcomp A (map-equiv e))
is-equiv-postcomp-univalence {X = X} A =
  ind-equiv X
    ( λ Y e → is-equiv (postcomp A (map-equiv e)))
    ( is-equiv-id (A → X))

-- Theorem 15.2.2

weak-funext-univalence :
  {l : Level} {A : UU l} {B : A → UU l} → WEAK-FUNEXT A B
weak-funext-univalence {A = A} {B} is-contr-B =
  is-contr-retract-of
    ( fib (postcomp A (pr1 {B = B})) id)
    ( pair
      ( λ f → pair (λ x → pair x (f x)) refl)
      ( pair
        ( λ h x → tr B (htpy-eq (pr2 h) x) (pr2 (pr1 h x)))
        ( refl-htpy)))
    ( is-contr-map-is-equiv
      ( is-equiv-postcomp-univalence A (equiv-pr1 is-contr-B))
      ( id))

funext-univalence :
  {l : Level} {A : UU l} {B : A → UU l} (f : (x : A) → B x) → FUNEXT f
funext-univalence {A = A} {B} f =
  FUNEXT-WEAK-FUNEXT (λ A B → weak-funext-univalence) A B f

--------------------------------------------------------------------------------

-- Section 15.3 Finite sets

is-finite-Prop :
  {l : Level} → UU l → UU-Prop l
is-finite-Prop X = trunc-Prop (count X)

is-finite :
  {l : Level} → UU l → UU l
is-finite X = type-Prop (is-finite-Prop X)

is-prop-is-finite :
  {l : Level} (X : UU l) → is-prop (is-finite X)
is-prop-is-finite X = is-prop-type-Prop (is-finite-Prop X)

is-finite' :
  {l : Level} → UU l → UU l
is-finite' X = Σ ℕ (λ n → type-trunc-Prop (Fin n ≃ X))

--
is-finite-empty : is-finite empty
is-finite-empty =
  unit-trunc-Prop
    ( Σ ℕ (λ n → Fin n ≃ empty))
    ( pair zero-ℕ (equiv-id empty))

𝔽 : UU (lsuc lzero)
𝔽 = Σ (UU lzero) is-finite

type-𝔽 : 𝔽 → UU lzero
type-𝔽 X = pr1 X

is-finite-type-𝔽 : (X : 𝔽) → is-finite (type-𝔽 X)
is-finite-type-𝔽 X = pr2 X

type-free-symmetric-monoid :
  {l1 : Level} (A : UU l1) → UU (lsuc lzero ⊔ l1)
type-free-symmetric-monoid A = Σ 𝔽 (λ X → type-𝔽 X → A)

map-universal-property-is-finite :
  {l1 l2 : Level} (X : UU l1) (P : UU-Prop l2) →
  ((n : ℕ) → (Fin n ≃ X) → type-Prop P) →
  is-finite X → type-Prop P
map-universal-property-is-finite X P f =
  map-universal-property-trunc-Prop P (ind-Σ f)

is-finite-is-finite :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  ((n : ℕ) → (Fin n ≃ X) → is-finite Y) →
  is-finite X → is-finite Y
is-finite-is-finite {l1} {l2} {X} {Y} f =
  map-universal-property-is-finite X (is-finite-Prop Y) f

is-finite-coprod :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  is-finite X → is-finite Y → is-finite (coprod X Y)
is-finite-coprod X Y is-finite-X is-finite-Y =
  is-finite-is-finite 
    ( λ n e →
      is-finite-is-finite 
        ( λ m f →
          unit-trunc-Prop _
            ( pair
              ( add-ℕ n m)
              ( ( equiv-coprod e f) ∘e (inv-equiv (coprod-Fin n m)))))
        is-finite-Y)
    ( is-finite-X)

--------------------------------------------------------------------------------

-- Subuniverses

is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU ((lsuc l1) ⊔ l2)
is-subuniverse P = is-subtype P

subuniverse :
  (l1 l2 : Level) → UU ((lsuc l1) ⊔ (lsuc l2))
subuniverse l1 l2 = Σ (UU l1 → UU l2) is-subuniverse

{- By univalence, subuniverses are closed under equivalences. -}
in-subuniverse-equiv :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P X → P Y
in-subuniverse-equiv P e = tr P (eq-equiv _ _ e)

in-subuniverse-equiv' :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P Y → P X
in-subuniverse-equiv' P e = tr P (inv (eq-equiv _ _ e))

total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) → UU ((lsuc l1) ⊔ l2)
total-subuniverse {l1} P = Σ (UU l1) (pr1 P)

{- We also introduce the notion of 'global subuniverse'. The handling of 
   universe levels is a bit more complicated here, since (l : Level) → A l are 
   kinds but not types. -}
   
is-global-subuniverse :
  (α : Level → Level) (P : (l : Level) → subuniverse l (α l)) →
  (l1 l2 : Level) → UU _
is-global-subuniverse α P l1 l2 =
  (X : UU l1) (Y : UU l2) → X ≃ Y → (pr1 (P l1)) X → (pr1 (P l2)) Y

{- Next we characterize the identity type of a subuniverse. -}

Eq-total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → UU l1
Eq-total-subuniverse (pair P H) (pair X p) t = X ≃ (pr1 t)

Eq-total-subuniverse-eq :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  (s t : total-subuniverse P) → Id s t → Eq-total-subuniverse P s t
Eq-total-subuniverse-eq (pair P H) (pair X p) .(pair X p) refl = equiv-id X

abstract
  is-contr-total-Eq-total-subuniverse :
    {l1 l2 : Level} (P : subuniverse l1 l2)
    (s : total-subuniverse P) →
    is-contr (Σ (total-subuniverse P) (λ t → Eq-total-subuniverse P s t))
  is-contr-total-Eq-total-subuniverse (pair P H) (pair X p) =
    is-contr-total-Eq-substructure (is-contr-total-equiv X) H X (equiv-id X) p

abstract
  is-equiv-Eq-total-subuniverse-eq :
    {l1 l2 : Level} (P : subuniverse l1 l2)
    (s t : total-subuniverse P) → is-equiv (Eq-total-subuniverse-eq P s t)
  is-equiv-Eq-total-subuniverse-eq (pair P H) (pair X p) =
    fundamental-theorem-id
      ( pair X p)
      ( equiv-id X)
      ( is-contr-total-Eq-total-subuniverse (pair P H) (pair X p))
      ( Eq-total-subuniverse-eq (pair P H) (pair X p))

eq-Eq-total-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) →
  {s t : total-subuniverse P} → Eq-total-subuniverse P s t → Id s t
eq-Eq-total-subuniverse P {s} {t} =
  inv-is-equiv (is-equiv-Eq-total-subuniverse-eq P s t)

--------------------------------------------------------------------------------

-- Finite sets
    
{-
  map-universal-property-is-finite X 
    ( is-finite-Prop (coprod X Y))
    ( λ n e →
      map-universal-property-is-finite Y
        ( is-finite-Prop (coprod X Y))
        ( λ m f →
          unit-trunc-Prop _
            ( pair
              ( add-ℕ n m)
              ( equiv-functor-coprod e f ∘e
                inv-equiv (coprod-Fin n m))))
        is-finite-Y)
    is-finite-X
-}

is-finite-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-finite A → is-finite B
is-finite-is-equiv f is-equiv-f =
  is-finite-is-finite
    ( λ n e → unit-trunc-Prop _ (pair n ((pair f is-equiv-f) ∘e e)))

is-finite-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  is-finite A → is-finite B
is-finite-equiv (pair f is-equiv-f) = is-finite-is-equiv f is-equiv-f

{-
is-finite-is-equiv' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-equiv f → is-finite' A → is-finite' B
is-finite-is-equiv' f is-equiv-f (pair n e) =
  pair n ({!!}) 

is-finite-Π :
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  is-finite' A → ((x : A) → is-finite' (B x)) → is-finite' ((x : A) → B x)
is-finite-Π A B (pair zero-ℕ e) is-finite-B = pair one-ℕ {!!}
is-finite-Π A B (pair (succ-ℕ n) e) is-finite-B = {!!}
-}

{-
μ-free-symmetric-monoid :
  {l : Level} (A : UU l) →
  type-free-symmetric-monoid (type-free-symmetric-monoid A) →
  type-free-symmetric-monoid A
μ-free-symmetric-monoid A x = {!!}
-}

-- Classical logic in univalent type theory

{- Recall that a proposition P is decidable if P + (¬ P) holds. -}

classical-Prop :
  (l : Level) → UU (lsuc l)
classical-Prop l = Σ (UU-Prop l) (λ P → is-decidable (pr1 P))

{- We show that if A is a proposition, then so is is-decidable A. -}

is-prop-is-decidable :
  {l : Level} {A : UU l} → is-prop A → is-prop (is-decidable A)
is-prop-is-decidable is-prop-A =
  is-prop-coprod intro-dn is-prop-A is-prop-neg

{- Not every type is decidable. -}

case-elim :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  ¬ B → coprod A B → A
case-elim nb (inl a) = a
case-elim nb (inr b) = ex-falso (nb b)

simplify-not-all-2-element-types-decidable :
  {l : Level} →
  ((X : UU l) (p : type-trunc-Prop (bool ≃ X)) → is-decidable X) →
  ((X : UU l) (p : type-trunc-Prop (bool ≃ X)) → X)
simplify-not-all-2-element-types-decidable d X p =
  case-elim
    ( map-universal-property-trunc-Prop
      ( dn-Prop' X)
      ( λ e → intro-dn (map-equiv e true))
      ( p))
    ( d X p)

{-
not-all-2-element-types-decidable :
  {l : Level} → ¬ ((X : UU l) (p : type-trunc-Prop (bool ≃ X)) → is-decidable X)
not-all-2-element-types-decidable d = {!simplify-not-all-2-element-types-decidable d (raise _ bool) ?!}

not-all-types-decidable :
  {l : Level} → ¬ ((X : UU l) → is-decidable X)
not-all-types-decidable d =
  not-all-2-element-types-decidable (λ X p → d X)
-}

{- Decidable equality of Fin n. -}

has-decidable-equality-empty : has-decidable-equality empty
has-decidable-equality-empty ()

has-decidable-equality-unit :
  has-decidable-equality unit
has-decidable-equality-unit star star = inl refl

decidable-Eq-Fin :
  (n : ℕ) (i j : Fin n) → classical-Prop lzero
decidable-Eq-Fin n i j =
  pair
    ( pair (Id i j) (is-set-Fin n i j))
    ( has-decidable-equality-Fin n i j)

{- Decidable equality of ℤ. -}

has-decidable-equality-ℤ : has-decidable-equality ℤ
has-decidable-equality-ℤ =
  has-decidable-equality-coprod
    has-decidable-equality-ℕ
    ( has-decidable-equality-coprod
      has-decidable-equality-unit
      has-decidable-equality-ℕ)

{- Closure of decidable types under retracts and equivalences. -}

has-decidable-equality-retract-of :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  A retract-of B → has-decidable-equality B → has-decidable-equality A
has-decidable-equality-retract-of (pair i (pair r H)) d x y =
  is-decidable-retract-of
    ( Id-retract-of-Id (pair i (pair r H)) x y)
    ( d (i x) (i y))

-- Exercises

-- Exercise 15.1

tr-equiv-eq-ap : {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A}
  (p : Id x y) → (map-equiv (equiv-eq (ap B p))) ~ tr B p
tr-equiv-eq-ap refl = refl-htpy

-- Exercise 15.2

subuniverse-is-contr :
  {i : Level} → subuniverse i i
subuniverse-is-contr {i} = pair is-contr is-subtype-is-contr

unit' :
  (i : Level) → UU i
unit' i = pr1 (Raise i unit)

abstract
  is-contr-unit' :
    (i : Level) → is-contr (unit' i)
  is-contr-unit' i =
    is-contr-equiv' unit (pr2 (Raise i unit)) is-contr-unit

abstract
  center-UU-contr :
    (i : Level) → total-subuniverse (subuniverse-is-contr {i})
  center-UU-contr i =
    pair (unit' i) (is-contr-unit' i)
  
  contraction-UU-contr :
    {i : Level} (A : Σ (UU i) is-contr) →
    Id (center-UU-contr i) A
  contraction-UU-contr (pair A is-contr-A) =
    eq-Eq-total-subuniverse subuniverse-is-contr
      ( equiv-is-contr (is-contr-unit' _) is-contr-A)

abstract
  is-contr-UU-contr : (i : Level) → is-contr (Σ (UU i) is-contr)
  is-contr-UU-contr i =
    pair (center-UU-contr i) (contraction-UU-contr)

is-trunc-UU-trunc :
  (k : 𝕋) (i : Level) → is-trunc (succ-𝕋 k) (Σ (UU i) (is-trunc k))
is-trunc-UU-trunc k i X Y =
  is-trunc-is-equiv k
    ( Id (pr1 X) (pr1 Y))
    ( ap pr1)
    ( is-emb-pr1-is-subtype
      ( is-prop-is-trunc k) X Y)
    ( is-trunc-is-equiv k
      ( (pr1 X) ≃ (pr1 Y))
      ( equiv-eq)
      ( univalence (pr1 X) (pr1 Y))
      ( is-trunc-equiv-is-trunc k (pr2 X) (pr2 Y)))

is-set-UU-Prop :
  (l : Level) → is-set (UU-Prop l)
is-set-UU-Prop l = is-trunc-UU-trunc (neg-one-𝕋) l

ev-true-false :
  {l : Level} (A : UU l) → (f : bool → A) → A × A
ev-true-false A f = pair (f true) (f false)

map-universal-property-bool :
  {l : Level} {A : UU l} →
  A × A → (bool → A)
map-universal-property-bool (pair x y) true = x
map-universal-property-bool (pair x y) false = y

issec-map-universal-property-bool :
  {l : Level} {A : UU l} →
  ((ev-true-false A) ∘ map-universal-property-bool) ~ id
issec-map-universal-property-bool (pair x y) =
  eq-pair-triv (pair refl refl)

isretr-map-universal-property-bool' :
  {l : Level} {A : UU l} (f : bool → A) →
  (map-universal-property-bool (ev-true-false A f)) ~ f
isretr-map-universal-property-bool' f true = refl
isretr-map-universal-property-bool' f false = refl

isretr-map-universal-property-bool :
  {l : Level} {A : UU l} →
  (map-universal-property-bool ∘ (ev-true-false A)) ~ id
isretr-map-universal-property-bool f =
  eq-htpy (isretr-map-universal-property-bool' f)

universal-property-bool :
  {l : Level} (A : UU l) →
  is-equiv (λ (f : bool → A) → pair (f true) (f false))
universal-property-bool A =
  is-equiv-has-inverse
    map-universal-property-bool
    issec-map-universal-property-bool
    isretr-map-universal-property-bool

ev-true :
  {l : Level} {A : UU l} → (bool → A) → A
ev-true f = f true

triangle-ev-true :
  {l : Level} (A : UU l) →
  (ev-true) ~ (pr1 ∘ (ev-true-false A))
triangle-ev-true A = refl-htpy

aut-bool-bool :
  bool → (bool ≃ bool)
aut-bool-bool true = equiv-id bool
aut-bool-bool false = equiv-neg-𝟚

bool-aut-bool :
  (bool ≃ bool) → bool
bool-aut-bool e = map-equiv e true

decide-true-false :
  (b : bool) → coprod (Id b true) (Id b false)
decide-true-false true = inl refl
decide-true-false false = inr refl

eq-false :
  (b : bool) → (¬ (Id b true)) → (Id b false)
eq-false true p = ind-empty (p refl)
eq-false false p = refl

eq-true :
  (b : bool) → (¬ (Id b false)) → Id b true
eq-true true p = refl
eq-true false p = ind-empty (p refl)

Eq-𝟚-eq : (x y : bool) → Id x y → Eq-𝟚 x y
Eq-𝟚-eq x .x refl = reflexive-Eq-𝟚 x

eq-false-equiv' :
  (e : bool ≃ bool) → Id (map-equiv e true) true →
  is-decidable (Id (map-equiv e false) false) → Id (map-equiv e false) false
eq-false-equiv' e p (inl q) = q
eq-false-equiv' e p (inr x) =
  ind-empty
    ( Eq-𝟚-eq true false
      ( ap pr1
        ( eq-is-contr
          ( is-contr-map-is-equiv (is-equiv-map-equiv e) true)
          ( pair true p)
          ( pair false (eq-true (map-equiv e false) x)))))

-- Exercise 14.11

square-htpy-eq :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B) →
  ( g h : B → C) →
  ( (λ (p : (y : B) → Id (g y) (h y)) (x : A) → p (f x)) ∘ htpy-eq) ~
  ( htpy-eq ∘ (ap (precomp f C)))
square-htpy-eq f g .g refl = refl

is-emb-precomp-is-surjective :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-surjective f → (C : UU-Set l3) → is-emb (precomp f (type-Set C))
is-emb-precomp-is-surjective {f = f} is-surj-f C g h =
  is-equiv-top-is-equiv-bottom-square
    ( htpy-eq)
    ( htpy-eq)
    ( ap (precomp f (type-Set C)))
    ( λ p a → p (f a))
    ( square-htpy-eq f g h)
    ( funext g h)
    ( funext (g ∘ f) (h ∘ f))
    ( dependent-universal-property-surj-is-surjective f is-surj-f
      ( λ a → Id-Prop C (g a) (h a)))

{-
eq-false-equiv :
  (e : bool ≃ bool) → Id (map-equiv e true) true → Id (map-equiv e false) false
eq-false-equiv e p =
  eq-false-equiv' e p (has-decidable-equality-𝟚 (map-equiv e false) false)
-}

{-
eq-true-equiv :
  (e : bool ≃ bool) →
  ¬ (Id (map-equiv e true) true) → Id (map-equiv e false) true
eq-true-equiv e f = {!!}

issec-bool-aut-bool' :
  ( e : bool ≃ bool) (d : is-decidable (Id (map-equiv e true) true)) →
  htpy-equiv (aut-bool-bool (bool-aut-bool e)) e
issec-bool-aut-bool' e (inl p) true =
  ( htpy-equiv-eq (ap aut-bool-bool p) true) ∙ (inv p)
issec-bool-aut-bool' e (inl p) false =
  ( htpy-equiv-eq (ap aut-bool-bool p) false) ∙
  ( inv (eq-false-equiv e p))
issec-bool-aut-bool' e (inr f) true =
  ( htpy-equiv-eq
    ( ap aut-bool-bool (eq-false (map-equiv e true) f)) true) ∙
  ( inv (eq-false (map-equiv e true) f))
issec-bool-aut-bool' e (inr f) false =
  ( htpy-equiv-eq (ap aut-bool-bool {!eq-true-equiv e ?!}) {!!}) ∙
  ( inv {!!})

issec-bool-aut-bool :
  (aut-bool-bool ∘ bool-aut-bool) ~ id
issec-bool-aut-bool e =
  eq-htpy-equiv
    ( issec-bool-aut-bool' e
      ( has-decidable-equality-𝟚 (map-equiv e true) true))
-}
