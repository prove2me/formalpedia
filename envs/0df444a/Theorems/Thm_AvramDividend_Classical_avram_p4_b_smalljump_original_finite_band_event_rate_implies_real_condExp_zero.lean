-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_event_rate_implies_real_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_event_rate_implies_real_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:25:12.65217+00:00
-- url     : https://prove2.me/theorems/fd8649c5-9457-47af-b285-16d64b583191
-- title:
--   Actual Lévy finite-band ENNReal event rates imply centred real conditional expectation
-- statement:
--   For the exact original Lévy intrinsic marked jump count on a fixed time interval and mark band, a finite real first moment plus the right-continuous ENNReal event-rate identity imply zero conditional expectation of the centred real count in the original right-continuous filtration. This supplies the ENNReal-to-real bridge required for compensated finite-band martingale differences. It assumes the actual P2 event-rate, count finite almost surely and integrable.
-- source:
--   Mathlib integrable_toReal_of_lintegral_ne_top, integral_toReal, integral_sub and ENNReal.toReal_mul, together with accepted source rightCont all-event conditional-expectation zero theorem a3b46bfb.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_event_means_imply_condExp_zero

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_event_rate_implies_real_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J : Ω → ℝ≥0∞)
    (hJsource : ∀ ω, J ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B))
    (hJmeas : Measurable J)
    (hJfinite : ∀ᵐ ω ∂P, J ω < ⊤)
    (hJint : Integrable (fun ω => (J ω).toReal) P)
    (rate : ℝ≥0∞)
    (hRate : ∀ A : Set Ω,
      MeasurableSet[𝓕.rightCont s] A →
      (∫⁻ ω in A, J ω ∂P) = P A * rate) :
    P[(fun ω => (J ω).toReal - rate.toReal) | 𝓕.rightCont s] =ᵐ[P] 0 := by sorry
