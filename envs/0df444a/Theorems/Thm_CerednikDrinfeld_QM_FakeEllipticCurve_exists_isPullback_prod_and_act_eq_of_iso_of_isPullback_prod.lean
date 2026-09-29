-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_prod_and_act_eq_of_iso_of_isPullback_prod
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_prod_and_act_eq_of_iso_of_isPullback_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/d7b91724-0471-59ac-bc60-92fac702913d
-- title:
--   Transport of a product structure along an isomorphism
-- statement:
--   Fix natural numbers $M,N$, a commutative ring $S$, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$, and two fake elliptic curves $E_1 : \mathrm{FakeEllipticCurve}\ \Lambda\ M\ S$ and $A_0 : \mathrm{FakeEllipticCurve}\ \Lambda\ N\ S$, each carrying a scheme, a structure morphism to $\operatorname{Spec} S$, a relative group law on its functor of points $\mathrm{SchemeHomOver}$, and an action $\mathrm{act}$ of $\Lambda$ by endomorphisms over $S$. Fix further a scheme $A$ with $f : A \to \operatorname{Spec} S$ and a relative group law $L$ on $f$; rationals $c,d$ and an order $O \subseteq \mathbb{H}[\mathbb{Q},c,d]$ (containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning, finitely generated); a family $\varepsilon$ of endomorphisms of $A$ over $S$ indexed by $O$, which are homomorphisms for $L$ on points, with $\varepsilon(1)=\mathrm{id}$, $\varepsilon(xy)=\varepsilon(y)$ followed by $\varepsilon(x)$, and $\varepsilon(x+y)$ acting as the $L$-product of $\varepsilon(x)$ and $\varepsilon(y)$; and a $\mathbb{Q}$-algebra map $j : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{H}[\mathbb{Q},c,d])$ carrying $\Lambda$ into matrices with entries in $O$. The hypotheses on $E_1$ constitute a product structure: morphisms $p_1,p_2 : E_1.A \to A$ over $S$ making $E_1.A$ the fibre product $A \times_{\operatorname{Spec} S} A$ (as an `IsPullback` square for $f,f$), both projections being homomorphisms on points; a family $\mathbf{E}(y)$ of endomorphisms of $E_1.A$ over $S$, indexed by matrices $y \in M_2(\mathbb{H}[\mathbb{Q},c,d])$ with entries in $O$, whose projections along $p_1,p_2$ are given by the expected $2\times 2$ matrix formula in the $\varepsilon(y_{il})$; the identity $E_1.\mathrm{act}(m) = \mathbf{E}(j(m))$ for $m \in \Lambda$; and the laws that each $\mathbf{E}(y)$ is a homomorphism on points, $\mathbf{E}(1)=\mathrm{id}$, $\mathbf{E}(yy') = \mathbf{E}(y')$ followed by $\mathbf{E}(y)$, and $\mathbf{E}(y+y')$ is the pointwise $E_1.L$-product of $\mathbf{E}(y)$ and $\mathbf{E}(y')$. Finally, assume given $u : A_0.A \to E_1.A$ over $S$ and $u' : E_1.A \to A_0.A$ with $u \circ$-inverse to $u'$ on both sides, $u$ a homomorphism from $A_0.L$ to $E_1.L$ on points, and $A_0.\mathrm{act}(x)$ followed by $u$ equal to $u$ followed by $E_1.\mathrm{act}(x)$ for all $x \in \Lambda$. The conclusion asserts the existence of morphisms $p_1,p_2 : A_0.A \to A$ over $S$ and a family $\mathbf{E}$ of endomorphisms of $A_0.A$ over $S$ indexed as above, satisfying verbatim the same list of clauses with $A_0$ in place of $E_1$: the cartesian square over $f,f$, homomorphy of both projections, the matrix formula in the $\varepsilon(y_{il})$, the compatibility $A_0.\mathrm{act}(m) = \mathbf{E}(j(m))$, and homomorphy, unitality, reversed multiplicativity and additivity of $\mathbf{E}$.
--
--   This is the transport statement for the product description of a fake elliptic curve: a fake elliptic curve whose underlying scheme is a fibre product $A \times_S A$ with a matrix action of an order, and whose $\Lambda$-action is induced by an embedding $j$ into $M_2$, passes this whole package to any isomorphic fake elliptic curve of a possibly different level. It is used in the construction of the fake elliptic curve with full endomorphism dictionary over a base in which $2$ is a unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_prod_and_act_eq_of_iso_of_isPullback_prod.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_QuaternionAlgebra_Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_prod_and_act_eq_of_iso_of_isPullback_prod
    {M N : ℕ} (S : Type) [CommRing S]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (E₁ : FakeEllipticCurve Λ M S) (A₀ : FakeEllipticCurve Λ N S)

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
    (p₁ p₂ : E₁.A ⟶ A) (hp₁ : p₁ ≫ f = E₁.f) (hp₂ : p₂ ≫ f = E₁.f) (hpb : CategoryTheory.IsPullback p₁ p₂ f f)
    (hp_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E₁.f),
      mapPt p₁ hp₁ (E₁.L.mul t P Q) = L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q) ∧
      mapPt p₂ hp₂ (E₁.L.mul t P Q) = L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q))
    (E : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ i l, y i l ∈ O) → (E₁.A ⟶ E₁.A))
    (hE : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), E y hy ≫ E₁.f = E₁.f)
    (hE_mat : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E₁.f),
      mapPt p₁ hp₁ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (mapPt p₂ hp₂ P)) ∧
      mapPt p₂ hp₂ (pushPt (E y hy) (hE y hy) P) =
        L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (mapPt p₂ hp₂ P)))
    (hact : ∀ m : ↥Λ, E₁.act m = E (j (m : ℍ[ℚ, a, b])) (hj m))
    (hE_hom : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
        {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E₁.f),
      pushPt (E y hy) (hE y hy) (E₁.L.mul t P Q) = E₁.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y hy) (hE y hy) Q))
    (hE_one : ∀ h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O, E 1 h1 = 𝟙 E₁.A)
    (hE_mul : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y * y') i l ∈ O), E (y * y') hyy' = E y' hy' ≫ E y hy)
    (hE_add : ∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
        (hyy' : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E₁.f),
      pushPt (E (y + y') hyy') (hE _ hyy') P = E₁.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y' hy') (hE y' hy') P))

    (u : A₀.A ⟶ E₁.A) (u' : E₁.A ⟶ A₀.A) (hu : u ≫ E₁.f = A₀.f)
    (huu' : u ≫ u' = 𝟙 A₀.A) (hu'u : u' ≫ u = 𝟙 E₁.A)
    (hu_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
      mapPt u hu (A₀.L.mul t P Q) = E₁.L.mul t (mapPt u hu P) (mapPt u hu Q))
    (hu_act : ∀ x : ↥Λ, A₀.act x ≫ u = u ≫ E₁.act x) :
    ∃ (p₁ p₂ : A₀.A ⟶ A) (hp₁ : p₁ ≫ f = A₀.f) (hp₂ : p₂ ≫ f = A₀.f)
      (E : ∀ y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d], (∀ i l, y i l ∈ O) → (A₀.A ⟶ A₀.A))
      (hE : ∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O), E y hy ≫ A₀.f = A₀.f),

      CategoryTheory.IsPullback p₁ p₂ f f ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
        mapPt p₁ hp₁ (A₀.L.mul t P Q) = L.mul t (mapPt p₁ hp₁ P) (mapPt p₁ hp₁ Q) ∧
        mapPt p₂ hp₂ (A₀.L.mul t P Q) = L.mul t (mapPt p₂ hp₂ P) (mapPt p₂ hp₂ Q)) ∧

      (∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
          {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A₀.f),
        mapPt p₁ hp₁ (pushPt (E y hy) (hE y hy) P) =
          L.mul t (pushPt (ε ⟨y 0 0, hy 0 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 0 1, hy 0 1⟩) (hε _) (mapPt p₂ hp₂ P)) ∧
        mapPt p₂ hp₂ (pushPt (E y hy) (hE y hy) P) =
          L.mul t (pushPt (ε ⟨y 1 0, hy 1 0⟩) (hε _) (mapPt p₁ hp₁ P)) (pushPt (ε ⟨y 1 1, hy 1 1⟩) (hε _) (mapPt p₂ hp₂ P))) ∧

      (∀ m : ↥Λ, A₀.act m = E (j (m : ℍ[ℚ, a, b])) (hj m)) ∧

      (∀ (y : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O)
          {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A₀.f),
        pushPt (E y hy) (hE y hy) (A₀.L.mul t P Q) = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y hy) (hE y hy) Q)) ∧
      (∀ h1 : ∀ i l, (1 : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) i l ∈ O, E 1 h1 = 𝟙 A₀.A) ∧
      (∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
          (hyy' : ∀ i l, (y * y') i l ∈ O), E (y * y') hyy' = E y' hy' ≫ E y hy) ∧
      (∀ (y y' : Matrix (Fin 2) (Fin 2) ℍ[ℚ, c, d]) (hy : ∀ i l, y i l ∈ O) (hy' : ∀ i l, y' i l ∈ O)
          (hyy' : ∀ i l, (y + y') i l ∈ O) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t A₀.f),
        pushPt (E (y + y') hyy') (hE _ hyy') P = A₀.L.mul t (pushPt (E y hy) (hE y hy) P) (pushPt (E y' hy') (hE y' hy') P)) := by sorry
