-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_growth_20261123_zeroSigma_original_killed_exit_budget
-- name    : AvramDividend.Classical.avram_growth_20261123_zeroSigma_original_killed_exit_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T08:12:40.935113+00:00
-- url     : https://prove2.me/theorems/f50e5721-e991-42ab-bb92-67c48d8b59ee
-- title:
--   Original infinite cap killed HJB first exit budget, Pure jump zero diffusion
-- statement:
--   Exact original spectrally negative Levy killed first exit expected verification budget. The additional original diffusion-coefficient case hypothesis is pure jump zero. No stochastic budget or new growth bound is assumed.
-- source:
--   Original main Avram mission HJB growth source 9dbe8433-2987-4c67-b9af-45cd3df5aba8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_growth_20261123_zeroSigma_original_killed_exit_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hTop : C = ⊤) (hw0 : 0 ≤ w 0)
    (hwcont : ContinuousOn w (Ici 0)) (hwneg : ∀ y < 0, w y = 0)
    (hwsmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwgen : ∀ y, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwgrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hSigma : X.σ = 0) :
    ∀ b : ℝ, 1 ≤ b →
      w b * (twoSidedExitExpectation X q b 1).toReal ≤ w 1 := by sorry
