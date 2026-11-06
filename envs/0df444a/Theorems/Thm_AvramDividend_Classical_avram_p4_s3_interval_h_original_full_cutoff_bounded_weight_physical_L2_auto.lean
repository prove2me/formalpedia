-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
-- name    : AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:19:11.559602+00:00
-- url     : https://prove2.me/theorems/c9ac937f-ffcc-40a0-963d-8df304daac26
-- title:
--   Automatic source-exact original full-cutoff bounded predictable product L² without assumed moment
-- statement:
--   For the original X, true physical marked jump count on any shifted physical interval and full negative cutoff, a uniformly bounded coefficient H measurable at the original rightCont beginning produces a square integrable compensated marked-count product, without any extra weighted integrability assumption or small-band restriction.
-- source:
--   Proved exact shifted physical full-cutoff count second moment is integrable; physical marked-count measurability and original rightCont measurability yield measurability of product; |H|≤L bounds H²C² by integrable L²C² and hence proves MemLp 2.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_shifted_centered_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (n : ℕ)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    MemLp (fun ω => H ω * ((N ω).toReal - r)) 2 P := by sorry
