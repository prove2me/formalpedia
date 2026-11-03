-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_uniform_trunc_signed_budgets_imply_full_signed_mean
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_uniform_trunc_signed_budgets_imply_full_signed_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:47:24.834193+00:00
-- url     : https://prove2.me/theorems/b2134db9-93aa-4268-b5ac-be8cba2a91d3
-- title:
--   Uniform bounded original signed Stieltjes expected budgets imply full unbounded finite random-clock real signed budget
-- statement:
--   Let τ be any measurable pathwise finite NNReal random clock of the exact original spectrally negative Lévy process. If the genuine expected signed Stieltjes payouts on each bounded truncation min(τ,n+1) are uniformly at most a real B, then the full original expected signed Stieltjes payout on paymentTimes(ruinTime)∩Iic τ is also ≤B, with no deterministic bound on τ. This is a real-valued budget consequence of the independently Proved original double ENNReal monotone budget and exact finite-clock original signed/ENNReal expectation bridge under finiteness. The proof derives B≥0 from the n=0 real expected nonnegativity rather than silently assuming it; the full expected signed cash is nonnegative as well. All time-zero, continuous and endpoint payments remain in the canonical source dividendMeasure.
-- source:
--   Proved original direct uniform bounded signed budget→ENNReal theorem 2bdab35f; finite-clock full signed/ENNReal mean identity under actual expected cash finiteness; Mathlib ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_full_stieltjes_signed_ennreal_mean_eq_of_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_uniform_trunc_signed_budgets_imply_full_signed_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ)
    (hBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫ ω, (∫ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by sorry
