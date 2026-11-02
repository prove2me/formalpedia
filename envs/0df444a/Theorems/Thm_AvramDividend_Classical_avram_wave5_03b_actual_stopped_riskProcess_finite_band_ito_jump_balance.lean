-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_riskProcess_finite_band_ito_jump_balance
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_stopped_riskProcess_finite_band_ito_jump_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:17:38.309359+00:00
-- url     : https://prove2.me/theorems/715ac87b-9e76-459c-811e-c995a8fa3873
-- title:
--   Actual original controlled riskProcess finite jump band satisfies the exact ruin-stopped nonlinear source Itô jump balance
-- statement:
--   For a finite collection T enumerating exactly original source X negative-mark jump instants on (s,t], the actual controlled prepayment reserve jump w(riskProcess_t)-w(leftLim riskProcess_t), localised to the interior reserve band and stopped inclusively at actual ruin, equals the sum of the correctly truncated source-linear jump and the genuine Levy generator Taylor remainder. This binds the nonlinear jump theorem directly to riskProcess rather than a proxy; a simultaneous right dividend payment is a separate chronological event. A finite enumeration T is explicitly assumed, not asserted almost surely.
-- source:
--   Canonical Proved 03-B finite actual source band algebra f32a1b6d-56e0-4784-a00f-d1d931bf0f6c; source exact riskProcess nonlinear jump bridge pending 03-B publication from canonical prepayment left-limit and source jumpmark results caa7f605, d2800259. No compensated martingale, abstract Poisson or control independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_finite_source_band_taylor_chain_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_prepayment_w_jump_exact_source_increment

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_stopped_riskProcess_finite_band_ito_jump_balance
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
        w (riskProcess X x D q ω) -
          w (Function.leftLim
            (fun r : ℝ≥0 => riskProcess X x D r ω) q)
        else 0) else 0) =
    (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if -1 < J q then
        J q * (if Y q ∈ Icc (u + δ) v then deriv w (Y q) else 0)
        else 0) +
      (if Y q ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y q) (J q)
        else 0) else 0) := by sorry
