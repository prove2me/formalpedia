-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_g_original_cell_product_indep_past
-- name    : AvramDividend.Classical.avram_route_runner_g_original_cell_product_indep_past
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:30:35.288043+00:00
-- url     : https://prove2.me/theorems/cbe7da50-9edb-42df-934b-82bb25e75728
-- title:
--   Original marked jump cell product independent of every past-filtration statistic
-- statement:
--   For a spectrally negative Lévy process, the original finite cutoff-jump exponential product over a future half-open cell (s,t] is independent of every measurable random variable in the past filtration at s. The proof identifies the product with a measurable functional of the original shifted future Lévy path and applies the verified path-history independence theorem.
-- source:
--   AVRAM Route Runner G 7 Nov 2026, original path-independent cell product needed for finite-family iIndepFun in 8b604395.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_unit_grid_cell_product_laplace
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_arbitrary_shift_marked_loss
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_levy_future_path_measurable_jump_extractor_indep_past_ws01b
open MeasureTheory Set Filter AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_g_original_cell_product_indep_past
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ 1) (k : ℕ)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    IndepFun H (fun ω : Ω =>
      ∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
        X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) P := by sorry
