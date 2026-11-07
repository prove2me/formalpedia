-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_HJB_killed_upcross_expectation_bound
-- name    : AvramDividend.Classical.avram_p4_f6_original_HJB_killed_upcross_expectation_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T09:31:08.470506+00:00
-- url     : https://prove2.me/theorems/8d1164b7-10ee-4fad-92a7-4f012f12ed91
-- title:
--   Original HJB supermartingale bounds the strictly killed discounted upper-exit expectation
-- statement:
--   For original nonzero Gaussian and jump spectrally negative Lévy, any smooth q-excessive HJB supersolution with gradient floor satisfies w(b) times the corrected discounted probability of upper exit before ruin from reserve 1 no greater than w(1), for b≥1. Requires genuinely stopped generator inequality, integrability, and correct 0/ruin boundary.
-- source:
--   Mathematical optional-stopping component of original killed HJB comparison fe2d23f9, split off independently from q-scale first-exit ratio. Exact corrected original two-sided exit transform, no surrogate process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_original_HJB_killed_upcross_expectation_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∀ b : ℝ, 1 ≤ b →
      w b * (twoSidedExitExpectationCorrected X q b 1).toReal ≤ w 1 := by sorry
