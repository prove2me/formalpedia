-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_localRing_eq_localization_of_affineModel_of_map_maximalIdeal_le_of_isIntegrallyClosed_ofPrime
-- name    : AlgebraicGeometry.exists_localRing_eq_localization_of_affineModel_of_map_maximalIdeal_le_of_isIntegrallyClosed_ofPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/3d5d10da-0211-5948-a663-92dd8431d926
-- title:
--   Local rings of an affine model arise on the proper model
-- statement:
--   Let $A_0$ be a discrete valuation ring, let $X_0$ be an integral scheme and let $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ be proper, flat and locally of finite presentation, with every stalk $\mathcal O_{X_0,y}$ integrally closed. Let $F_0$ be a field which is an $A_0$-algebra, together with a ring isomorphism $\varphi_0 : F_0 \cong K(X_0)$ onto the function field (the stalk at the generic point) carrying $a \in A_0$ to the germ at the generic point of the global section pulled back along $\mathrm{toBase}_0$; for $x \in X_0$ write $\mathcal O_x \subseteq F_0$ for the image under $\varphi_0^{-1}$ of the image of $\mathcal O_{X_0,x}$ in $K(X_0)$. Assume: (i) every point $\eta$ of the special fibre ($\mathrm{toBase}_0(\eta)$ the closed point of $\operatorname{Spec} A_0$) which is non-closed, in the sense that $\eta$ specialises to some point distinct from itself, specialises only to points $y$ that are closed ($y \rightsquigarrow z$ forces $z = y$); (ii) for each such $\eta$ the subring $\mathcal O_\eta$ of $F_0$ is the underlying subring of a valuation subring of $F_0$. Let $B$ be a finitely generated $A_0$-subalgebra of $F_0$ with fraction field $F_0$ (every $x \in F_0$ satisfies $xc = b$ for some $b, c \in B$, $c \neq 0$), such that every prime of $B$ containing $\mathfrak m_{A_0}B$ and not maximal is a minimal prime of $\mathfrak m_{A_0}B$; assume further that for each non-closed $\eta$ in the special fibre with $B \subseteq \mathcal O_\eta$ there is a prime $\mathfrak q$ of $B$ with $\mathcal O_\eta = B_{\mathfrak q}$ inside $F_0$, and conversely that each minimal prime $\mathfrak q$ of $\mathfrak m_{A_0}B$ equals $\mathcal O_\eta$ in this sense for some non-closed $\eta$ in the special fibre. Then for every prime $\mathfrak p$ of $B$ containing $\mathfrak m_{A_0}B$ such that the localisation of $B$ at $\mathfrak p$, regarded as a local subring of $F_0$, is integrally closed, there is a point $x \in X_0$ with $\mathcal O_x = B_{\mathfrak p}$ inside $F_0$, i.e. $f \in \mathcal O_x$ if and only if $fc = b$ for some $b, c \in B$ with $c \notin \mathfrak p$.
--
--   This is the form of Zariski's main theorem used to recognise points of a proper normal model of a curve over a discrete valuation ring by their local rings in the function field: a prime of an affine model lying over the maximal ideal of $A_0$, at which the model is normal, is the centre of a (unique) point of the proper model with the same local ring, the normality being required only at the prime in question. It is applied in the construction of charts at the special fibre of models of modular curves of full level, in the analysis of points specialising from a node.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_localRing_eq_localization_of_affineModel_of_map_maximalIdeal_le_of_isIntegrallyClosed_ofPrime.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_localRing_eq_localization_of_affineModel_of_map_maximalIdeal_le_of_isIntegrallyClosed_ofPrime
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

    (B : Subalgebra A₀ F₀) (hBfg : B.FG)
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
    (𝔭 : Ideal ↥B) [𝔭.IsPrime] (h𝔭 : Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭)

    (hBpn : IsIntegrallyClosed ↥(LocalSubring.ofPrime B.toSubring 𝔭).toSubring) :
    ∃ x : X₀, ∀ f : F₀, f ∈ SemistableModel.localRing X₀ φ₀ x ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀) := by sorry
