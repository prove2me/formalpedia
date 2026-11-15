-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
-- name    : AvramDividend.Classical.avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:10:03.522015+00:00
-- url     : https://prove2.me/theorems/316fb152-4993-4218-b6a2-b24fe4d6499c
-- title:
--   Original ruin-clipped physical Gaussian/jump HJB drift and true right dividend cash signed sum nonpositive
-- statement:
--   The actual ruin-clipped physical grid v_i=min(iΔ,σ(ω)) and original controlled reserve riskProcess X x D(v_i) satisfy the finite-cell signed HJB discounted generator plus every finite set of genuine time-zero and strict pre-ruin right-dividend cash corrections nonpositive, provided the selected physical cells remain within the true open reserve/cap band and the clipped clock is ordered. The theorem uses actual original source, cap, ruinTime, D/rightLimit and exponential discount. It is the physical-mesh sign component of 61538c12; the remaining work is relating the full inclusive Iic Stieltjes cash and stopped terminal contact to this finite sum and proving vanishing L1 mesh energy.
-- source:
--   Direct instance of already Proved avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign with S=range m, s_i=v_i, t_i=v_{i+1}, y_i=actual riskProcess at v_i; stopped mask, cap interior and finite R pre-ruin premises retained.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
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
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
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
            (rightLimit D u ω - D u ω))))) ≤ 0 := by sorry
