-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_localRing_eq_localization_of_normal_affineModel_of_relDimOne_of_val_of_gen
-- name    : AlgebraicGeometry.existsUnique_localRing_eq_localization_of_normal_affineModel_of_relDimOne_of_val_of_gen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/d2667254-7f29-592f-9766-8eaa6b11d2f6
-- title:
--   Normal relative curve: stalks are localisations of an affine model
-- statement:
--   Let $A_0$ be a discrete valuation ring, let $X_0$ be an integral scheme with a morphism $\mathrm{toBase}_0 : X_0 \to \operatorname{Spec} A_0$ that is proper, flat and locally of finite presentation, and assume every stalk of $X_0$ is integrally closed. Let $F_0$ be a field that is an $A_0$-algebra together with a ring isomorphism $\varphi_0 : F_0 \cong K(X_0)$ onto the function field carrying $\mathrm{algebraMap}\ A_0\ F_0$ to the canonical map $A_0 \to \mathcal{O}(X_0) \to K(X_0)$; for $x \in X_0$ write $\mathcal{O}_x \subseteq F_0$ for the image under $\varphi_0^{-1}$ of the stalk at $x$ inside $K(X_0)$. Assume: (hdim) every point $y \ne \eta$ to which a non-closed point $\eta$ of the special fibre specialises is closed; (hval) $\mathcal{O}_\eta$ is a valuation subring of $F_0$ for every such $\eta$; (hgenX) every valuation subring $V \ne F_0$ containing $(\mathrm{algebraMap}\ A_0\ F_0\ a)^{-1}$ for all $a \ne 0$ equals some $\mathcal{O}_y$. Let $B \subseteq F_0$ be a finitely generated $A_0$-subalgebra, integrally closed in $F_0$, with $F_0$ as its field of fractions, such that (hdimB) every non-maximal prime of $B$ containing $\mathfrak{m}_{A_0}B$ is minimal over $\mathfrak{m}_{A_0}B$, (hgenB) $B_{\mathfrak p}$ is a valuation subring for every nonzero prime $\mathfrak p \not\supseteq \mathfrak{m}_{A_0}B$, and (hcomp, hcomp') the rings $\mathcal{O}_\eta$ for non-closed $\eta$ on the special fibre contained in $B$ correspond exactly to localisations of $B$ at primes minimal over $\mathfrak{m}_{A_0}B$. Then for every prime $\mathfrak p$ of $B$ there is a unique $x \in X_0$ with $\mathcal{O}_x = B_{\mathfrak p}$ (as the set of $f \in F_0$ with $fc = b$ for some $b, c \in B$, $c \notin \mathfrak p$), and this $x$ lies in the smooth locus of $\mathrm{toBase}_0$ if and only if $A_0 \to B_{\mathfrak p}$ is formally smooth.
--
--   This is the local comparison step identifying the points and stalks of a normal proper flat model of relative dimension one over a discrete valuation ring with the prime spectrum and localisations of a normal affine model $B$ with the same fraction field, together with the recognition of the smooth locus. It is used in the construction of semistable models of modular curves of full level over the relevant descent base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_localRing_eq_localization_of_normal_affineModel_of_relDimOne_of_val_of_gen.lean

import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_localRing_eq_localization_of_normal_affineModel_of_relDimOne_of_val_of_gen
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

    (hgenX : ∀ V : ValuationSubring F₀, V ≠ ⊤ → (∀ a : A₀, a ≠ 0 → (algebraMap A₀ F₀ a)⁻¹ ∈ V) →
      ∃ y : X₀, V.toSubring = SemistableModel.localRing X₀ φ₀ y)

    (B : Subalgebra A₀ F₀) (hBfg : B.FG) (hBn : ∀ x : F₀, _root_.IsIntegral ↥B x → x ∈ B)
    (hBfrac : ∀ x : F₀, ∃ b c : F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b)

    (hdimB : ∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
      𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes)

    (hgenB : ∀ 𝔭 : Ideal ↥B, 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) →
      ∃ V : ValuationSubring F₀, ∀ f : F₀, f ∈ V ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀))

    (hcomp : ∀ η : X₀, toBase₀.base η = closedPoint A₀ → (∃ y : X₀, η ⤳ y ∧ y ≠ η) →
      (B : Set F₀) ⊆ SemistableModel.localRing X₀ φ₀ η →
        ∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔
          ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : F₀) = (b : F₀))
    (hcomp' : ∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
      ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧
        ∀ x : F₀, x ∈ SemistableModel.localRing X₀ φ₀ η ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : F₀) = (b : F₀)) :
    ∀ (𝔭 : Ideal ↥B) [𝔭.IsPrime],
      ∃ x : X₀, (∀ f : F₀, f ∈ SemistableModel.localRing X₀ φ₀ x ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀)) ∧
        (∀ x' : X₀, (∀ f : F₀, f ∈ SemistableModel.localRing X₀ φ₀ x' ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : F₀) = (b : F₀)) → x' = x) ∧
        (x ∈ toBase₀.smoothLocus ↔ (algebraMap A₀ (Localization.AtPrime 𝔭)).FormallySmooth) := by sorry
