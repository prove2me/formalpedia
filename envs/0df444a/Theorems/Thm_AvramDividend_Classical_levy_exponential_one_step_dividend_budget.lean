-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_one_step_dividend_budget
-- name    : AvramDividend.Classical.levy_exponential_one_step_dividend_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:33:37.782745+00:00
-- url     : https://prove2.me/theorems/202f5f63-4f66-4a98-8f1a-23332454de0a
-- title:
--   Discounted one-step Lévy exponential payoff plus cash dividend is bounded by initial exponential capital
-- statement:
--   Let X be a spectrally negative Lévy process and θ≥1. Suppose its Laplace exponent ψ(θ) is at most q, and an immediate dividend a is paid from deterministic starting reserve u, with 0≤a≤u. After a nonnegative deterministic time t of Lévy evolution from the post-dividend reserve u-a, the sum of cash a and the discounted expectation of the positive exponential candidate at the new reserve is bounded by exp(θu). Combine the already Proved exponential transition eigenfunction, the exponent inequality tψ≤tq and the already Proved exponential dividend secant bound. This is a genuine deterministic-horizon stochastic step but does not assert arbitrary stopping, adapted strategies or an Itô verification formula.
-- source:
--   Proved exponential transition eigenfunction and exp_dividend_secant_bound; elementary Mathlib positivity and exponential monotonicity.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction
import Theorems.Thm_AvramDividend_Classical_exp_dividend_secant_bound

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exponential_one_step_dividend_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ q u a : ℝ)
    (hθ : 1 ≤ θ) (ha : 0 ≤ a) (hua : a ≤ u)
    (hψ : X.ψ θ ≤ q) :
    a + Real.exp (-(t : ℝ) * q) *
        (∫ ω, Real.exp (θ * (u - a + X.X t ω)) ∂P) ≤
      Real.exp (θ * u) := by sorry
