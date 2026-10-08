-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_root_finite_laplace_package
-- name    : AvramDividend.Classical.bv_esscher_root_finite_laplace_package
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T12:52:30.019346+00:00
-- url     : https://prove2.me/theorems/554eca76-84a9-4881-a6dc-40f927e96479
-- title:
--   Finite positive root-shifted renewal measure with tilted scale Laplace identity
-- statement:
--   At the positive Esscher root φ satisfying ψφ=q in the BV standing Lévy case, construct a positive finite measure β with finite cumulative masses whose cumulative's exponentially weighted real Laplace integrals exactly equal those of the tilted scale function e^(-φx)W(x) for all sufficiently large Laplace variables θ. This is a strictly smaller stochastic renewal construction obligation than identifying β's cumulative pointwise with the tilted scale. The latter follows from the already Proved continuous_rightContinuous_Ioi_eq_of_laplace_eq once scale continuity and nonnegativity are supplied by IsScaleFunction. Root subcriticality and finite geometric convolution total mass can be proved via the separately authored lemmas.
-- source:
--   Proved canonical BV Lévy–Khintchine and geometric positive renewal packages, root-shifted Laplace kernel, and uniqueness of one-sided Laplace transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_esscher_root_finite_laplace_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ (β : Measure ℝ) (b : ℝ),
      0 < β Set.univ ∧ β Set.univ ≠ ⊤ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ θ : ℝ, b < θ →
        IntegrableOn
          (fun x : ℝ => Real.exp (-θ * x) *
            (Real.exp (-(φ * x)) * W x)) (Ioi 0) ∧
        IntegrableOn
          (fun x : ℝ => Real.exp (-θ * x) *
            (β (Iic x)).toReal) (Ioi 0) ∧
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
            (Real.exp (-(φ * x)) * W x)) =
          (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
            (β (Iic x)).toReal)) := by sorry
