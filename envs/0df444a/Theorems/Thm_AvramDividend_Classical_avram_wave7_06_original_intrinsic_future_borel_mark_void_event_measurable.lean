-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:19:52.759318+00:00
-- url     : https://prove2.me/theorems/0b92926a-dd94-426e-b2d3-7f10249bc06b
-- title:
--   Exact intrinsic original future marked-jump void event is measurable
-- statement:
--   For any original spectrally negative Lévy process, every Borel mark set B and finite interval (s,t], the event that its literal left-jump intrinsic count is zero is measurable on the original sample space. The proof combines the already proved same-path measurable count extractor and measurable shifted original future path. No probabilistic law is assumed.
-- source:
--   W7-06 source intrinsic marked zero-event measurability needed to convert future-void indicator factorisation to P-event independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_future_borel_mark_void_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    MeasurableSet {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = 0} := by sorry
