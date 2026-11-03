-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor
-- name    : AvramDividend.Classical.avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:22:20.848643+00:00
-- url     : https://prove2.me/theorems/d860de51-66c0-4abb-b2a1-0fa5cbd23835
-- title:
--   Actual original future marked-void event probability factors from past
-- statement:
--   For a genuine original spectrally negative Lévy process, every measurable source-past event A and every future Borel marked void event are probabilistically independent. The theorem states the actual P(A∩void)=P(A)P(void) equality for literal X.X jump counts. The source-void measurable event and an extended nonnegative indicator factorisation are proved as separate dependencies, with raw A-measurability explicitly included.
-- source:
--   W7-06 original negative-band future void independence, direct input to Poisson zero count time semigroup; exact source X and P.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_intrinsic_future_mark_void_event_probability_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (A : Set Ω) (hApast : MeasurableSet[𝓕 s] A)
    (hAraw : MeasurableSet A) :
    P (A ∩ {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = 0}) =
    P A * P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) = 0} := by sorry
