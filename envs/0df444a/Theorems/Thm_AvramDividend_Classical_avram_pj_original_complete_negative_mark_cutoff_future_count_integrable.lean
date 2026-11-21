-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_complete_negative_mark_cutoff_future_count_integrable
-- name    : AvramDividend.Classical.avram_pj_original_complete_negative_mark_cutoff_future_count_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T10:14:41.82887+00:00
-- url     : https://prove2.me/theorems/d6077ae7-3cd8-4697-ac25-8f7524186e5a
-- title:
--   Original full negative-mark finite-cutoff compensated future physical marked count is automatically L1
-- statement:
--   Under the original spectrally negative Lévy process probability, the complete negative finite cutoff jump count on every deterministic future physical interval, centred by its exact non-Gaussian Lévy intensity, is integrable. Follows from the Proved original full-cutoff bounded predictable weighted L2 theorem instantiated with constant weight one, then L2-to-L1 on the original probability space. Removes the integrable future count hypothesis from the full negative-mark conditional cross-mean argument.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_physical_L2_auto
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_complete_negative_mark_cutoff_future_count_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (cut : ℕ) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    Integrable (fun ω => (N ω).toReal - r) P := by sorry
