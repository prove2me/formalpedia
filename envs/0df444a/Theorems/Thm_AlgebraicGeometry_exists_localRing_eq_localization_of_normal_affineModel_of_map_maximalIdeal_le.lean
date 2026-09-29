-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le
-- name    : AlgebraicGeometry.exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/2617b08f-c64d-5e60-a060-d53f2d224a5d
-- title:
--   Localisations of an affine model are local rings of the proper model
-- statement:
--   Let $A_0$ be a discrete valuation ring, let $X_0$ be an integral scheme and $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ a proper, flat, locally finitely presented morphism all of whose stalks $\mathcal O_{X_0,y}$ are integrally closed. Let $F_0$ be a field with an $A_0$-algebra structure and $\varphi_0 : F_0 \cong K(X_0)$ a ring isomorphism carrying the image of each $a \in A_0$ to the germ at the generic point of the global section obtained from $a$ by pullback along $\mathrm{toBase}_0$; write $\mathcal O_{X_0,x} \subseteq F_0$ for the image under $\varphi_0^{-1}$ of the canonical image of the stalk at $x$ in $K(X_0)$. Assume: every point $y \neq \eta$ specialising from a point $\eta$ of the special fibre that is not itself closed has no proper specialisations; every such non-closed special point $\eta$ has $\mathcal O_{X_0,\eta}$ equal to the underlying subring of a valuation subring of $F_0$. Let $B \subseteq F_0$ be a finitely generated $A_0$-subalgebra which is integrally closed in $F_0$ and has $F_0$ as its field of fractions, such that every non-maximal prime of $B$ containing $\mathfrak m_{A_0}B$ is a minimal prime of $\mathfrak m_{A_0}B$. Assume further that for every non-closed special point $\eta$ with $B \subseteq \mathcal O_{X_0,\eta}$ there is a prime $\mathfrak q$ of $B$ with $\mathcal O_{X_0,\eta} = B_{\mathfrak q}$ inside $F_0$, and conversely that every minimal prime $\mathfrak q$ of $\mathfrak m_{A_0}B$ arises as $\mathcal O_{X_0,\eta} = B_{\mathfrak q}$ for some non-closed special point $\eta$. Then for every prime $\mathfrak p$ of $B$ containing $\mathfrak m_{A_0}B$ there exists $x \in X_0$ with $\mathcal O_{X_0,x} = B_{\mathfrak p}$ as subrings of $F_0$, i.e. $f \in \mathcal O_{X_0,x}$ if and only if $f = b/c$ with $b, c \in B$, $c \notin \mathfrak p$.
--
--   This is the form of Zariski's main theorem needed for the birational correspondence $\operatorname{Spec} B \dashrightarrow X_0$: a point of the affine normal model lying over the closed point of $\operatorname{Spec} A_0$ is the centre of a point of the proper normal model with the same local ring. It is used, together with a uniqueness statement, to transfer explicit affine charts to the proper semistable models of modular curves occurring later in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_localRing_eq_localization_of_normal_affineModel_of_map_maximalIdeal_le
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (hn₀ : ∀ y : X₀, IsIntegrallyClosed (X₀.presheaf.stalk y))
    {F₀ : Type} [Field F₀] [Algebra A₀ F₀]
    (φ₀ : F₀ ≃+* X₀.functionField)
    (hφ₀ : ∀ a : A₀, φ₀ (algebraMap A₀ F₀ a) = SemistableModel.baseToFunctionField toBase₀ a)

    (hdim : ∀ η y : X₀, toBase₀.base η = closedPoint A₀ → (∃ z : X₀, η ⤳ z ∧ z ≠ η) → η ⤳ y → y ≠ η →
      ∀ z : X₀, y ⤳ z → z = y)

    (hval : ∀ η : X₀, toBase₀.base η = closedPoint A₀ → (∃ y : X₀, η ⤳ y ∧ y ≠ η) →
      ∃ V : ValuationSubring F₀, V.toSubring = SemistableModel.localRing X₀ φ₀ η)

    (B : Subalgebra A₀ F₀) (hBfg : B.FG) (hBn : ∀ x : F₀, _root_.IsIntegral ↥B x → x ∈ B)
    (hBfrac : ∀ x : F₀, ∃ b c : F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b)

    (hdimB : ∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
      𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes)

    (hcomp : ∀ η : X₀, toBase₀.base η = closedPoint A₀ → (∃ y : X₀, η ⤳ y ∧ y ≠ η) →
      (B : Set F₀) ⊆ SemistableModel.localRing X₀ φ₀ η →
        ∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔
          ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : F₀) = (b : F₀))
    (hcomp' : ∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
      ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧
        ∀ x : F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : F₀) = (b : F₀))
    (𝔭 : Ideal ↥B) [𝔭.IsPrime] (h𝔭 : Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) :
    ∃ x : X₀, ∀ f : F₀, f ∈ SemistableModel.localRing X₀ φ₀ x ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀) := by sorry
