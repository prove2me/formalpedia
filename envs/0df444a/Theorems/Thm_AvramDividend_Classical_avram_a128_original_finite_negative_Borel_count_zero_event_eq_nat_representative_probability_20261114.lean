-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a128_original_finite_negative_Borel_count_zero_event_eq_nat_representative_probability_20261114
-- name    : AvramDividend.Classical.avram_a128_original_finite_negative_Borel_count_zero_event_eq_nat_representative_probability_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:41:19.347386+00:00
-- url     : https://prove2.me/theorems/69180353-b6a7-480f-84a4-cee4d52d7f2b
-- title:
--   Original finite-intensity negative Borel physical zero-jump event agrees in probability with its measurable integer-count representative
-- statement:
--   At finite negative Lévy activity, the physical actual Borel marked jump count is finite almost surely. If a measurable integer-valued representative K agrees almost surely with its real-valued count, then the probability of no original physical B-marked jump is exactly P(K=0). This avoids wrongly identifying ENNReal.toReal infinity with zero by explicitly using the source almost-sure finite count first.
-- source:
--   Proved JA34 expected ENNReal original Borel count rate, Proved p2_e_compensator_finite_nu_count_ae_finite and hFinite;  plus finite count and measure_congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a128_original_finite_negative_Borel_count_zero_event_eq_nat_representative_probability_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B) = 0} =
      P {ω : Ω | K ω = 0} := by sorry
