-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_finite_source_band_taylor_chain_sum
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_stopped_finite_source_band_taylor_chain_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:38:54.24407+00:00
-- url     : https://prove2.me/theorems/f32a1b6d-56e0-4784-a00f-d1d931bf0f6c
-- title:
--   Finite actual-source jump band admits exact ruin-stopped prepayment nonlinear Taylor chain-rule sum
-- statement:
--   For the original spectrally negative Lévy source and adapted dividends, assume a finite set T enumerates exactly those original X jump times in (s,t] whose literal left-jump source mark belongs to a negative band B. The ruin-stopped, reserve-localised sum of nonlinear prepayment jump increments then equals the sum of the generator truncation's linear source terms and the true source Lévy generator Taylor integrands. The proof is an exact finite chronological source-jump identity and does not replace the actual source measure by an unrelated Poisson model. It does not assert finiteness a.s., stochastic compensation, or right-payment Stieltjes corrections, which remain separate.
-- source:
--   Pointwise actual-source controlled prepayment Taylor-generator identity e336f7e2-a55f-48e8-b33e-54114f97e681 and original prepayment reserve mark equality d2800259-b627-4fd5-b139-985adba4e243. Finite support T exactly enumerates actual X jump marks in B and (s,t]. No independent jump measure, no source intensity assumption, no division by stochastic compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_stopped_finite_source_band_taylor_chain_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (T : Finset ℝ≥0)
    (hT : ∀ q : ℝ≥0, q ∈ T ↔
      s < q ∧ q ≤ t ∧
        X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q ∈ B) :
    let Y : ℝ≥0 → ℝ := fun q => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) q
    let J : ℝ≥0 → ℝ := fun q =>
      X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
    (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y q ∈ Icc (u + δ) v then
        w (Y q + J q) - w (Y q) else 0) else 0) =
    (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if -1 < J q then
        J q * (if Y q ∈ Icc (u + δ) v then deriv w (Y q) else 0)
        else 0) +
      (if Y q ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y q) (J q)
        else 0) else 0) := by sorry
