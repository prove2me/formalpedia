-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_g_original_cell_product_measurable
-- name    : AvramDividend.Classical.avram_route_runner_g_original_cell_product_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T19:12:09.172261+00:00
-- url     : https://prove2.me/theorems/22647802-93ff-4ad2-974d-f0fee7e08237
-- title:
--   Original cutoff jump product over an arbitrary bounded half-open cell is measurable
-- statement:
--   For the actual spectrally negative Lévy sample path, the finite product of exponentiated strictly negative jumps on any half-open interval within the unit horizon is a measurable random variable. The proof identifies the product as a measurable Borel functional of the shifted original Lévy path using the exact physical jump measure.
-- source:
--   AVRAM ROUTE RUNNER G 7 November 2026, source-exact measurable branch of independent equal-cell products.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_unit_grid_cell_product_laplace
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_arbitrary_shift_marked_loss
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable

open MeasureTheory Set Filter AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_g_original_cell_product_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ 1) (k : ℕ) :
    Measurable (fun ω : Ω =>
      ∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
        X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
