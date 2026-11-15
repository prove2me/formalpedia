-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_physical_ruinclipped_discrete_Ito_cash_with_signed_drift
-- name    : AvramDividend.Classical.avram_b24_original_physical_ruinclipped_discrete_Ito_cash_with_signed_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:22:43.609421+00:00
-- url     : https://prove2.me/theorems/d56dd3e6-cb26-4aa3-a187-39718c83ed22
-- title:
--   Exact original ruin-clipped physical stopped cash mesh inequality under signed Ito cell ledger
-- statement:
--   Original stopped Lévy physical mesh v_i=min(iΔ,σ) with true ruin-clipped discounting and right Stieltjes dividends: if every per-cell Ito ledger inequality holds and aggregate signed drift equals the original generator and right dividend corrections, the full terminal reward plus zero-time and all interval cash is bounded by initial reward plus Gaussian, compensated jump and Taylor error. Uses original X,D and actual physical times.
-- source:
--   Proved B239 exact physical generator and right payment combined negative; Proved aggregate cash telescope cb669445.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_physical_ruinclipped_discrete_Ito_cash_with_signed_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ η (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D t η - D t η ≤
        w (riskProcess X x D t η) -
          w (riskProcess X x D t η -
            (rightLimit D t η - D t η)))
    (σ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω)
    (active : ℕ → Bool)
    (hInterior : ∀ i ∈ Finset.range m, active i = true →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      let z := riskProcess X x D (v i) ω
      0 < z ∧ ENNReal.ofReal z < C)
    (hTimes : ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      v i ≤ v (i + 1))
    (R : Finset ℝ≥0)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω)
    (V cash gaussian jump drift error : ℕ → ℝ) (cash0 : ℝ)
    (hInitial : V 0 + cash0 ≤ w x)
    (hCell : ∀ i : ℕ, i < m →
      V (i + 1) + cash i ≤
        V i + gaussian i + jump i + drift i + error i)
    (hDrift : (∑ i ∈ Finset.range m, drift i) =
      (let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
       let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
       (∑ i ∈ Finset.range m, if active i then
         Real.exp (-(q * (v i : ℝ))) *
           ((v (i + 1) : ℝ) - (v i : ℝ)) *
           (X.generator w (riskProcess X x D (v i) ω) -
             q * w (riskProcess X x D (v i) ω))
         else 0) +
       (∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
         ((rightLimit D u ω - D u ω) -
           (w (riskProcess X x D u ω) -
             w (riskProcess X x D u ω -
               (rightLimit D u ω - D u ω))))))) :
    V m + cash0 + (∑ i ∈ Finset.range m, cash i) ≤
      w x + (∑ i ∈ Finset.range m, gaussian i) +
        (∑ i ∈ Finset.range m, jump i) +
        (∑ i ∈ Finset.range m, error i) := by sorry
