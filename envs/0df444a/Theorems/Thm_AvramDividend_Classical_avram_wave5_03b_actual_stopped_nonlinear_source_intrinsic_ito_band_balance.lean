-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_nonlinear_source_intrinsic_ito_band_balance
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_stopped_nonlinear_source_intrinsic_ito_band_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:30:38.647201+00:00
-- url     : https://prove2.me/theorems/f7b177c9-7d40-4cd8-bb02-7605d9d07a21
-- title:
--   Literal original BV/UBV stopped nonlinear source Ito balance with signed intrinsic Levy marked jump integral
-- statement:
--   For the genuine original spectrally negative Lévy X and adapted dividend D, on every finite negative source band separated from zero, construct exactly the original source jump times and establish a stopped nonlinear reserve jump chain rule expressed as a linear compensated-mark sum plus the signed Bochner integral against the literal original intrinsic marked source jump measure. Prove the signed marked kernel integrable on that same source fibre, retaining inclusive ruin source marks and the prepayment reserve.
-- source:
--   03B canonical Proved original finite-band automatically enumerated stopped nonlinear chain rule 42443bab, original signed intrinsic finite-band kernel integrability and equality 55f66f79 (must become Proved before publication), original source Taylor=generator pointwise e336f7e2. No Gaussian or Stieltjes control terms (owned Chat 03) and no Poisson-copy substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_C2_signed_intrinsic_separated_band_eq_finite_source_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_stopped_nonlinear_source_intrinsic_ito_band_balance
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
    let G : ℝ≥0 × ℝ → ℝ := fun p =>
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 ∈ B then HS ((p.1,ω),p.2) else 0
    let L : ℝ≥0 → ℝ := fun r =>
      if -1 < J r ω then
        J r ω * (if Y (r,ω) ∈ Icc (u + δ) v then deriv w (Y (r,ω)) else 0)
      else 0
    ∃ T : Finset ℝ≥0,
      (∀ r : ℝ≥0, r ∈ T ↔ s < r ∧ r ≤ t ∧ J r ω ∈ B) ∧
      Integrable G (NX ω) ∧
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        (if Y (r,ω) ∈ Icc (u + δ) v then
          w (riskProcess X x D r ω) -
          w (Function.leftLim (fun q : ℝ≥0 => riskProcess X x D q ω) r)
        else 0) else 0) =
      (∑ r ∈ T, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then L r else 0) +
      (∫ p : ℝ≥0 × ℝ, G p ∂NX ω) := by sorry
