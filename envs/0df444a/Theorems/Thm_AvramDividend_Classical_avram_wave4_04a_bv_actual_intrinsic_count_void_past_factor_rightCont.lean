-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_count_void_past_factor_rightCont
-- name    : AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_count_void_past_factor_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:17:25.046708+00:00
-- url     : https://prove2.me/theorems/0a1c6e27-ab94-4112-85d5-64b3ed651ca7
-- title:
--   Actual intrinsic original Lévy negative-jump measure has future void events independent of the right-continuous past
-- statement:
--   The event that the genuine original-source negative-jump counting measure N_X has no atom in a future time-mark rectangle (s,t]×(-∞,0) factors in measure from every A measurable in the original right-continuous past 𝓕.rightCont s, under BV and finite jump activity. This directly concerns the true marked counting measure on the same Ω/𝓕, not a constructed Poisson process. It is a conditional void probability identity, not a full predictable compensator.
-- source:
--   Exact all-sample pathwise N_X-rectangle zero iff no original jump 4087af7c, plus original right-cont past nojump event factorization b8ae0e83. Set ext identifies the two events, then transfers the factorization. Both source provider theorems must be canonically Proved before uploading the proof; no complete count law is asserted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_count_void_past_factor_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕.rightCont s) A) :
    P (A ∩ {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) = 0}) =
      P A * P {ω : Ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ Iio (0 : ℝ)) = 0} := by sorry
