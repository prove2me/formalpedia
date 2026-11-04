-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_signed_past_weighted_real_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_signed_past_weighted_real_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:36:37.115755+00:00
-- url     : https://prove2.me/theorems/fc91754b-0e46-4da0-8bb7-ff6bbf36d195
-- title:
--   Signed original predictable-simple marked jump weights have integrable real compensated expectation
-- statement:
--   For the actual source Lévy jump measure on (s,t]×B of finite ν-mass, any pair of nonnegative F_s-measurable weights with finite means defines a real signed predictable-simple mark count as the difference of its positive and negative weighted counts. This real function is integrable, and its expectation equals the difference of the separate prescribed Lévy rate products, assuming only the independently established unconditional original ν-rate. This gives a signed L¹ extension needed for BV/UBV stochastic compensation.
-- source:
--   P2-E source weighted real-L1 lemma and weighted real mean (new independently checked helpers), Mathlib integral_sub. External P2-D ν-rate remains Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_integrable_past_weighted_count
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_weighted_count_real_mean

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_signed_past_weighted_real_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (Wpos Wneg : Ω → ℝ≥0∞)
    (hWpos : Measurable[𝓕 s] Wpos)
    (hWneg : Measurable[𝓕 s] Wneg)
    (hPosFinite : (∫⁻ ω, Wpos ω ∂P) < ⊤)
    (hNegFinite : (∫⁻ ω, Wneg ω ∂P) < ⊤)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)) :
    Integrable (fun ω =>
      (Wpos ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      (Wneg ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal) P ∧
    (∫ ω,
      (Wpos ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      (Wneg ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ∂P) =
      ((∫⁻ ω, Wpos ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal -
      ((∫⁻ ω, Wneg ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal := by sorry
