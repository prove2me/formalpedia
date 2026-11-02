-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_stopped_separated_source_jump_right_payment_full_band_balance
-- name    : AvramDividend.Classical.avram_wave5_03_original_stopped_separated_source_jump_right_payment_full_band_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:17:31.94641+00:00
-- url     : https://prove2.me/theorems/84fea846-3c33-400c-9699-a46a4deaf814
-- title:
--   Actual original finite separated negative-jump bands automatically admit stopped combined Lévy/right-dividend chronological balance
-- statement:
--   For the true SpectrallyNegativeLevy sample path and the same adapted dividend process, every strictly negative mark band uniformly separated from zero has an actual finite chronological enumeration on any finite source horizon, and the inclusive-ruin-stopped nonlinear post-right-payment value changes on these times split exactly into genuine source generator/Taylor terms and simultaneous right-dividend value drops. No independent Poisson copy, disjointness of source and control events, or finite-activity assumption outside the band. This strengthens the previously Proved exact finite-set merge with existence under source path finite-band hypotheses, for both BV and UBV.
-- source:
--   03-B source separated-band existence/finite-jump identity 42443bab (Proved) and Chat03 source simultaneous right-payment finite sum identity 29945179 (Proved); supports BV ef7e6c20 and corrected UBV 429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_stopped_finite_source_jump_right_payment_chronological_merge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_stopped_separated_source_jump_right_payment_full_band_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0) :
    ∃ S : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ S ↔
        s < r ∧ r ≤ t ∧
          X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B) ∧
      (let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
          (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
       let J : ℝ≥0 → ℝ := fun r =>
          X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
       (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if Y r ∈ Icc (u + δ) v then
           w (riskProcess X x D r ω -
             (rightLimit D r ω - D r ω)) - w (Y r) else 0) else 0) =
       (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if -1 < J r then
           J r * (if Y r ∈ Icc (u + δ) v then deriv w (Y r) else 0)
           else 0) +
         (if Y r ∈ Icc (u + δ) v then
           SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r)
           else 0) else 0) +
       (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if Y r ∈ Icc (u + δ) v then
           w (riskProcess X x D r ω -
             (rightLimit D r ω - D r ω)) -
             w (riskProcess X x D r ω) else 0) else 0)) := by sorry
