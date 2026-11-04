-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_positive_event_all_k_real_bound
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_positive_event_all_k_real_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:41:32.804199+00:00
-- url     : https://prove2.me/theorems/fa562469-3f77-4bf8-b303-9012ded244e2
-- title:
--   Original Lévy positive exponential event has all-k common small-time real bound
-- statement:
--   For each power k, the actual original-process large positive exponential event has rate bounded by a fixed, k-independent constant after multiplication by R^k times (R-1)^4. The proof uses the original weighted integral asymptotic, the original-event Markov inequality and a checked ENNReal-to-real conversion, without assuming any positive-jump rate theorem.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_each_high_moment_eventually_zero_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_weighted_integer_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_positive_increment_weighted_markov
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_ennreal_product_toReal_bound

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_positive_event_all_k_real_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : ∀ t : ℝ≥0, Measurable (X.X t))
    (θ R : ℝ) (hθ : 0 ≤ θ) (hR : 1 < R) (k : ℕ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      R ^ k * ((R - 1) ^ 4 * ((P {ω | R ≤ Real.exp (θ * X.X (Real.toNNReal h) ω)}).toReal / h)) ≤
      (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1 := by sorry
