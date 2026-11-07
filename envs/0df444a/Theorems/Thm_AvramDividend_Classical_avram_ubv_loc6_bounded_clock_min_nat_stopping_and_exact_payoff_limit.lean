-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_bounded_clock_min_nat_stopping_and_exact_payoff_limit
-- name    : AvramDividend.Classical.avram_ubv_loc6_bounded_clock_min_nat_stopping_and_exact_payoff_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T07:41:58.279714+00:00
-- url     : https://prove2.me/theorems/e238c81f-f5c4-4968-9ec9-7e054023865b
-- title:
--   Natural capped stopping clocks are valid and give eventual exact physical payoff at any bounded horizon
-- statement:
--   Given an actual finite-horizon stopping time τ bounded by the integer n, σ_k=min(τ,k) stays a stopping time, never exceeds τ, and equals τ for every ω once k≥n. Consequently every exact stopped physical payoff function Pay evaluated at this very same σ_k, including the original right-limit reserve and closed-horizon Stieltjes cash, is eventually equal and converges in ENNReal.ofReal pointwise. The theorem does not assume payoff convergence or a value bound; integrability and the stopped Itô-Meyer budget remain separate genuine obligations.
-- source:
--   Avram UBV-LOC6 local-clock construction for the f7 clock/payoff/convergence child of fa7052b1. Pay can be instantiated with the exact discounted original terminal plus Iic dividendMeasure cash; uniform eventual equality avoids any truncation ambiguity at zero, a ruin jump, cap contact or the horizon atom.

import Mathlib

open MeasureTheory Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_bounded_clock_min_nat_stopping_and_exact_payoff_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (n : ℕ)
    (hBound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (hStop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (Pay : ℝ≥0 → Ω → ℝ) :
    (∀ k : ℕ, IsStoppingTime 𝓕
      (fun ω => ((min (τ ω) (k : ℝ≥0) : ℝ≥0) : WithTop ℝ≥0))) ∧
    (∀ k : ℕ, ∀ ω, min (τ ω) (k : ℝ≥0) ≤ τ ω) ∧
    (∀ ω, ∀ᶠ k : ℕ in Filter.atTop,
      min (τ ω) (k : ℝ≥0) = τ ω) ∧
    (∀ ω, Filter.Tendsto
      (fun k : ℕ => ENNReal.ofReal (Pay (min (τ ω) (k : ℝ≥0)) ω))
      Filter.atTop (nhds (ENNReal.ofReal (Pay (τ ω) ω)))) := by sorry
