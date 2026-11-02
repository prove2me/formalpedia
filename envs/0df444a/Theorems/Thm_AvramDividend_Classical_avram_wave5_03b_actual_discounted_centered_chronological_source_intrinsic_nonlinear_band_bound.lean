-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_discounted_centered_chronological_source_intrinsic_nonlinear_band_bound
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_discounted_centered_chronological_source_intrinsic_nonlinear_band_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:11:27.039209+00:00
-- url     : https://prove2.me/theorems/e139ca2f-24d4-485b-86d7-1e18ba2d465b
-- title:
--   Discounted original-source stopped nonlinear chronological finite-band Itô bound centred by the exact negative Lévy generator drift
-- statement:
--   For the actual spectrally negative Lévy X and adapted dividend D, the discounted stopped nonlinear chronological source jump plus right-payment correction on any separated negative source band is controlled by the discounted linear source increment and the original intrinsic signed jump integral, after subtracting the exact discounted true-X.ν negative-mark Taylor compensator drift. The compensator Taylor ν-drift is proved equal to the original generatorIntegrand ν-drift at the prepayment left reserve, for each time and hence under any time measure. The source jump at ruin is included and right dividend cash is strictly before ruin. This is an exact finite-band algebraic centred inequality. It does not assume a Poisson replacement or assert expectation-zero/martingale compensation.
-- source:
--   Canonical Proved c9de7cbf discounted original intrinsic finite-source chronological jump-plus-dividend inequality, and canonical Proved 5e3be45e original negative X.ν stopped Taylor-to-generator signed integral equality. Under the same X,D,Y and inclusive ruin stop, pointwise drift section equality and subtraction preserve the discounted chronological inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_discounted_chronological_source_intrinsic_nonlinear_band_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_discounted_centered_chronological_source_intrinsic_nonlinear_band_bound
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
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0)
    (μ : Measure ℝ≥0) :
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
    let S : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0
    let Driftq : ℝ≥0 → ℝ := fun r =>
      Real.exp (-(q * (r : ℝ))) *
        (∫ z in B, S r * H ((r,ω),z) ∂X.ν)
    let Genq : ℝ≥0 → ℝ := fun r =>
      Real.exp (-(q * (r : ℝ))) *
        (∫ z in B, S r *
          (if Y (r,ω) ∈ Icc (u + δ) v then
            SpectrallyNegativeLevy.generatorIntegrand w (Y (r,ω)) z else 0)
          ∂X.ν)
    ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable Gq (NX ω) ∧
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          Real.exp (-(q * (r : ℝ))) *
            ((w (W r) - w (Function.leftLim
              (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r)
        else 0) else 0) - (∫ r in Ioc s t, Driftq r ∂μ) ≤
      (∑ r ∈ T, Lq r) +
        ((∫ p : ℝ≥0 × ℝ, Gq p ∂NX ω) -
          (∫ r in Ioc s t, Genq r ∂μ)) := by sorry
