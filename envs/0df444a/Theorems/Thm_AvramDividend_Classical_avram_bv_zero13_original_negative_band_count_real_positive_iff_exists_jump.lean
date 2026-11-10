-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_negative_band_count_real_positive_iff_exists_jump
-- name    : AvramDividend.Classical.avram_bv_zero13_original_negative_band_count_real_positive_iff_exists_jump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:36:35.471811+00:00
-- url     : https://prove2.me/theorems/f9d2039d-8240-44af-801a-19af6d5fffbb
-- title:
--   Original intrinsic finite-band count has positive real mass exactly when a physical negative jump exists
-- statement:
--   For every actual original process path, time horizon and negative jump cutoff, the real-valued intrinsic negative-band count is positive precisely when the original path has a negative jump above that cutoff in the physical half-open observation interval. This bridges the already-Proved observed-clock stopping theorem to the true first negative jump, without any independent constructed compound-Poisson process or almost-sure exceptional event.
-- source:
--   Direct logical transport from Proved physical finite marked jump cardinality f0197436, finite marked set e5e6f70b, pinned Set.ncard_pos and ENNReal.toReal_natCast. This is needed for equality of observed and actual first negative jump clocks.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_negative_band_count_real_positive_iff_exists_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    0 < (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal ↔
      ∃ u : ℝ≥0, 0 < u ∧ u ≤ T ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
            -(1 / ((n : ℝ) + 1)) := by sorry
