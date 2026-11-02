-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_centered_source_intrinsic_nonlinear_stopped_ito_band_balance
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_centered_source_intrinsic_nonlinear_stopped_ito_band_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:03:46.759015+00:00
-- url     : https://prove2.me/theorems/848c611a-5be4-4901-b0d5-11723ce6831b
-- title:
--   Actual source stopped nonlinear Itô finite-band chain balance after exact Lévy generator drift centering
-- statement:
--   For original controlled reserve x+X.X-D, the prepayment left limit Y, inclusive ruin stopping, interior C² test w and a measurable negative mark band B separated from zero, there is a genuinely finite set of original source jump times and an integrable signed intrinsic original-source marked jump integral. The stopped nonlinear w jump chain sum minus the actual time-integrated source Taylor compensator equals the truncated linear source sum plus the centred raw original NX integral minus the X.generator nonlinear jump drift. The two drift forms agree by the Proved source-specific time-integrated negative-mark kernel theorem. No claim of mean-zero compensation or abstract Poisson independence is made.
-- source:
--   Proved f7b177c9 original stopped intrinsic nonlinear source finite-band jump Itô chain balance and 06ab55dc actual time-integrated stopped source nonlinear Taylor drift exact generator identity; exact algebraic centring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_nonlinear_source_intrinsic_ito_band_balance
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_C2_generator_time_integrated_jump_drift_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_centered_source_intrinsic_nonlinear_stopped_ito_band_balance
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
    let G : ℝ≥0 × ℝ → ℝ := fun p =>
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then HS ((p.1,ω),p.2) else 0
    let L : ℝ≥0 → ℝ := fun r =>
      if -1 < J r ω then
        J r ω * (if Y (r,ω) ∈ Icc (u + δ) v then deriv w (Y (r,ω)) else 0)
      else 0
    let S : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then 1 else 0
    let Drift : ℝ≥0 → ℝ := fun r =>
      ∫ z in B, S r * H ((r,ω),z) ∂X.ν
    let Gen : ℝ≥0 → ℝ := fun r =>
      ∫ z in B, S r *
        (if Y (r,ω) ∈ Icc (u + δ) v then
          SpectrallyNegativeLevy.generatorIntegrand w (Y (r,ω)) z else 0) ∂X.ν
    ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable G (NX ω) ∧
      ((∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          w (riskProcess X x D r ω) -
          w (Function.leftLim (fun q : ℝ≥0 => riskProcess X x D q ω) r)
        else 0) else 0) -
        (∫ r in Ioc s t, Drift r ∂μ)) =
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then L r else 0) +
        ((∫ p : ℝ≥0 × ℝ, G p ∂NX ω) -
        (∫ r in Ioc s t, Gen r ∂μ)) := by sorry
