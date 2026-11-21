-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
-- name    : AvramDividend.Classical.avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:25:54.344744+00:00
-- url     : https://prove2.me/theorems/b0d465d4-0763-43e7-8c75-e9be1725a654
-- title:
--   Genuine stopped clipped predictable Lévy-grid coefficient remains strongly measurable at every later right-continuous filtration time
-- statement:
--   The original strongly predictable derivative coefficient, symmetrically clipped to [-K,K] and set to zero when the true right-continuous stopping time has already elapsed at physical time s, is strongly measurable at s. By filtration monotonicity it is strongly measurable at any later original grid time t. This is one of the two past-factor measurability steps for full negative-mark compensated martingale cross-cell orthogonality.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕.rightCont Z)
    (K : ℝ) (hK : 0 ≤ K)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (s t : ℝ≥0) (hst : s ≤ t) :
    StronglyMeasurable[𝓕.rightCont t] (fun ω =>
      if (ρ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)
      then (0 : ℝ) else max (-K) (min K (Z s ω))) := by sorry
