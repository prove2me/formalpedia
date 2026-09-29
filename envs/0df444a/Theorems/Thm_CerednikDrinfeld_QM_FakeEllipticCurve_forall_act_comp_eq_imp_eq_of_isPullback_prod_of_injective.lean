-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_act_comp_eq_imp_eq_of_isPullback_prod_of_injective
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.forall_act_comp_eq_imp_eq_of_isPullback_prod_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/2e5e537d-384f-58e2-bb85-61714afda8e0
-- title:
--   Faithfulness of the centraliser order acting through E
-- statement:
--   Fix a natural number $N$, a commutative ring $S$, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ and a fake elliptic curve $A_0$ of level $N$ over $S$ for $\Lambda$ (a scheme $A_0.A$ with structure morphism $A_0.f$ to $\operatorname{Spec} S$, a commutative relative group law $A_0.L$ on its $T$-points, smoothness, properness, connected fibres, fibres of topological Krull dimension $2$, an action `act` of $\Lambda$ by endomorphisms over the base satisfying the group-law, unit, multiplicativity, additivity and trace conditions, and the level data). Fix further a scheme $A$ with $f : A \to \operatorname{Spec} S$ and a relative group law $L$ on $f$, rationals $c,d$ and a submodule $O \subseteq \mathbb{H}[\mathbb{Q},c,d]$ that is an order (contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},c,d]$ over $\mathbb{Q}$ and is finitely generated over $\mathbb{Z}$). Assume given $\varepsilon : O \to \operatorname{End}(A)$ with each $\varepsilon(x)$ over $f$, additive and multiplicative in the sense that on $T$-points $\varepsilon(x)$ is an $L$-homomorphism, $\varepsilon(1) = \mathrm{id}$, $\varepsilon(xy)$ is $\varepsilon(y)$ followed by $\varepsilon(x)$, and $\varepsilon(x+y)P = L(\varepsilon(x)P, \varepsilon(y)P)$; a $\mathbb{Q}$-algebra map $j : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{H}[\mathbb{Q},c,d])$ carrying $\Lambda$ into matrices with entries in $O$; morphisms $p_1, p_2 : A_0.A \to A$ over the base which are $L$-homomorphisms on points and exhibit $(p_1,p_2)$ as a pullback of $f$ against $f$; and an assignment $E$ sending each matrix $y$ with entries in $O$ to an endomorphism $E(y)$ of $A_0.A$ over $A_0.f$ such that $p_1 \circ E(y)$ and $p_2 \circ E(y)$ are computed on points by the matrix rule $p_i(E(y)P) = L\bigl(\varepsilon(y_{i0})(p_1 P), \varepsilon(y_{i1})(p_2 P)\bigr)$, such that $A_0.\mathrm{act}(m) = E(j(m))$ for $m \in \Lambda$, and such that $E(y)$ is an $A_0.L$-homomorphism, $E(1) = \mathrm{id}$, $E(yy')$ is $E(y')$ followed by $E(y)$, and $E(y+y')$ acts on points as the $A_0.L$-product of $E(y)$ and $E(y')$. Finally let $\tau : \mathbb{H}[\mathbb{Q},a_1,b_1] \to M_2(\mathbb{H}[\mathbb{Q},c,d])$ be an injective $\mathbb{Q}$-algebra map whose values commute with all $j(m)$, let $\varepsilon$ be injective, and let $R$ be a submodule of $\mathbb{H}[\mathbb{Q},a_1,b_1]$ characterised by: $x \in R$ if and only if every entry of $\tau(x)$ lies in $O$. Then for all $x,y \in R$, $E(\tau(x)) = E(\tau(y))$ implies $x = y$; that is, $x \mapsto E(\tau(x))$ is injective on $R$.
--
--   This is the faithfulness statement for the action of the centraliser order $R$ on the fake elliptic curve $A_0$ realised as a product via the pullback square: distinct elements of $R$ induce distinct endomorphisms of $A_0.A$. It feeds the construction of a fake elliptic curve with full endomorphism dictionary and formal module of height four over a base in which $2$ is invertible.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_forall_act_comp_eq_imp_eq_of_isPullback_prod_of_injective.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.forall_act_comp_eq_imp_eq_of_isPullback_prod_of_injective
    {N : ℕ} (S : Type) [CommRing S]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (A₀ : FakeEllipticCurve Λ N S)

    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {c d : ℚ} (O : Submodule ℤ ℍ[ℚ, c, d]) (hO : IsOrder O)
    (ε : ↥O → (A ⟶ A)) (hε : ∀ x : ↥O, ε x ≫ f = f)
    (hε_hom : ∀ (x : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      pushPt (ε x) (hε x) (L.mul t P Q) = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε x) (hε x) Q))
    (hε_one : ∀ h : (1 : ℍ[ℚ, c, d]) ∈ O, ε ⟨1, h⟩ = 𝟙 A)
    (hε_mul : ∀ (x y : ↥O) (h : (x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]) ∈ O),
      ε ⟨(x : ℍ[ℚ, c, d]) * (y : ℍ[ℚ, c, d]), h⟩ = ε y ≫ ε x)
    (hε_add : ∀ (x y : ↥O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      pushPt (ε (x + y)) (hε (x + y)) P = L.mul t (pushPt (ε x) (hε x) P) (pushPt (ε y) (hε y) P))

    (j : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hj : ∀ (m : ↥Λ) (i l : Fin 2), j (m : ℍ[ℚ, a, b]) i l ∈ O)
    (p₁ p₂ : A₀.A ⟶ A) (hp₁ : p₁ ≫ f = A₀.f) (hp₂ : p₂ ≫ f = A₀.f) (hpb : CategoryTheory.IsPullback p₁ p₂ f f)
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
      mapPt p₁ hp₁ (A₀.L.mul t P Q) = L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q) ∧
      mapPt p₂ hp₂ (A₀.L.mul t P Q) = L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q))
    (E : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ i l, y i l ∈ O) → (A₀.A ⟶ A₀.A))
    (hE : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), E y hy ≫ A₀.f = A₀.f)
    (hE_mat : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A₀.f),
      mapPt p₁ hp₁ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (mapPt p₂ hp₂ P)) ∧
      mapPt p₂ hp₂ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (mapPt p₂ hp₂ P)))
    (hact : ∀ m : ↥Λ, A₀.act m = E (j (m : ℍ[ℚ, a, b])) (hj m))
    (hE_hom : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
      pushPt (E y hy) (hE y hy) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y hy) (hE y hy) Q))
    (hE_one : ∀ h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O, E 1 h1 = 𝟙 A₀.A)
    (hE_mul : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y * y') i l ∈ O), E (y * y') hyy' = E y' hy' ≫ E y hy)
    (hE_add : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A₀.f),
      pushPt (E (y + y') hyy') (hE _ hyy') P = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y' hy') (hE y' hy') P))

    {a₁ b₁ : ℚ} (τ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hτ : Function.Injective τ)
    (hτj : ∀ (x : ℍ[ℚ, a₁, b₁]) (m : ℍ[ℚ, a, b]), τ x * j m = j m * τ x)
    (hε_inj : Function.Injective ε)
    (R : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hRiff : ∀ x : ℍ[ℚ, a₁, b₁], x ∈ R ↔ ∀ i l : Fin 2, τ x i l ∈ O) :
    ∀ x y : ↥R, E (τ (x : ℍ[ℚ, a₁, b₁])) ((hRiff _).1 x.2) = E (τ (y : ℍ[ℚ, a₁, b₁])) ((hRiff _).1 y.2) → x = y := by sorry
