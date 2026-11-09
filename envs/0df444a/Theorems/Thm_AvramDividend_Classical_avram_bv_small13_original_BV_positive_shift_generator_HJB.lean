-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_small13_original_BV_positive_shift_generator_HJB
-- name    : AvramDividend.Classical.avram_bv_small13_original_BV_positive_shift_generator_HJB
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:12:30.914656+00:00
-- url     : https://prove2.me/theorems/8b75d704-2d36-4f81-9c1b-2c0214276505
-- title:
--   Original BV spatially shifted generator HJB and gradient bound down to zero reserve
-- statement:
--   For the genuine original BV spectrally negative Levy source, shift a C1 interior HJB candidate spatially by any fixed positive delta. At every nonnegative controlled reserve y with y+delta strictly below the cap, the translated function retains the original generator integrability, the discounted HJB upper sign, and its derivative lower bound. This isolates an exact original-source boundary-removal interface, without a negative-generator global L1 assumption, auxiliary process, or zero-Stieltjes-cash claim. The cap owners must still establish the stopped original-process change-of-variable, terminal and payment chronology and delta-to-zero limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_small13_original_BV_positive_shift_generator_HJB
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      X.GeneratorIntegrable w z ∧ X.generator w z - q * w z ≤ 0)
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (δ y : ℝ) (hδ : 0 < δ) (hy : 0 ≤ y)
    (hcap : ENNReal.ofReal (y + δ) < C) :
    X.GeneratorIntegrable (fun v : ℝ => w (v + δ)) y ∧
      X.generator (fun v : ℝ => w (v + δ)) y - q * w (y + δ) ≤ 0 ∧
      1 ≤ deriv (fun v : ℝ => w (v + δ)) y := by sorry
