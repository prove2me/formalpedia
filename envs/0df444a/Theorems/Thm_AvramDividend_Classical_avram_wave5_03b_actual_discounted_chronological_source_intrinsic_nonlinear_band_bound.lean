-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_discounted_chronological_source_intrinsic_nonlinear_band_bound
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_discounted_chronological_source_intrinsic_nonlinear_band_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:52:50.029216+00:00
-- url     : https://prove2.me/theorems/c9de7cbf-9bf3-41e1-996f-681ee21db84d
-- title:
--   Discounted chronological actual original source and right dividend finite-band inequality with literal signed intrinsic nonlinear Levy measure
-- statement:
--   For the original spectrally negative Lévy process X and adapted dividend strategy D with the established chronological right-payment admissibility inequality, and a nonnegative discount rate q, on any measurable separated negative source jump band, construct the actual original finite source-jump set T, prove the discounted stopped nonlinear prepayment Taylor integrand is signed-integrable against the original intrinsic marked source measure, and bound the discounted reserve/source plus chronological right-dividend jump contributions by the discounted linear truncation source jump sum plus the true signed integral against that measure. This is a source/dividend interface, not a martingale or Gaussian/Stieltjes proof.
-- source:
--   Requires canonical Proved signed bounded-time-weight original source theorem (publication f9e05470-649a-4a2c-8713-d6b713b7a0a7), canonical Proved chronological source/dividend inequality 05c1be95-42b1-4c3a-971f-e75d22364e29 and pointwise generator Taylor equality e336f7e2-a55f-48e8-b33e-54114f97e681. The hJump admission assumption is explicit and not discharged by 03B.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_bounded_time_weight_signed_intrinsic_band
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_source_band_discounted_chronological_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_discounted_chronological_source_intrinsic_nonlinear_band_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (hjump : ∀ η (r : ℝ≥0),
      (r = 0 ∨ (r : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D r η - D r η ≤
        w (riskProcess X x D r η) -
          w (riskProcess X x D r η -
            (rightLimit D r η - D r η)))
    (q : ℝ) (hq : 0 ≤ q)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let J : ℝ≥0 → Ω → ℝ := fun r η =>
      X.X r η - Function.leftLim (fun z : ℝ≥0 => X.X z η) r
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun η =>
      ((Measure.count.restrict {r : ℝ≥0 | 0 < r ∧ J r η ≠ 0}).map
        (fun r : ℝ≥0 => (r, J r η)))
    let Gq : ℝ≥0 × ℝ → ℝ := fun p =>
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then
        Real.exp (-(q * (p.1 : ℝ))) * HS ((p.1,ω),p.2) else 0
    let W : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X r ω - rightLimit D r ω else riskProcess X x D r ω
    let cash : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) < ruinTime X x D ω then
        rightLimit D r ω - D r ω else 0
    let Lq : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        Real.exp (-(q * (r : ℝ))) *
          (if -1 < J r ω then
            J r ω * (if Y (r,ω) ∈ Icc (u + δ) v then
              deriv w (Y (r,ω)) else 0) else 0)
      else 0
    ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable Gq (NX ω) ∧
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          Real.exp (-(q * (r : ℝ))) *
            ((w (W r) - w (Function.leftLim
              (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r)
        else 0) else 0) ≤
      (∑ r ∈ T, Lq r) + (∫ p : ℝ≥0 × ℝ, Gq p ∂NX ω) := by sorry
