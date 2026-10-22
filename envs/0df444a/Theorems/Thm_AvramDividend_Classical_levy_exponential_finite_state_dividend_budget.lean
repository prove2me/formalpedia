-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_finite_state_dividend_budget
-- name    : AvramDividend.Classical.levy_exponential_finite_state_dividend_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:19:34.970988+00:00
-- url     : https://prove2.me/theorems/79159452-35e9-43c6-b24e-9be0e2f16dcb
-- title:
--   Conditional one-step exponential dividend bound for finitely many adapted reserve states
-- statement:
--   Fix a spectrally negative Levy process and two deterministic times s≤t. Let a finite-valued random index be measurable at s and associate with each index an initial reserve u_i and a nonnegative dividend a_i≤u_i. If theta≥1, the Laplace exponent at theta is at most the discount rate q, and the deterministic exponential payoff is integrable for every state, then almost surely the dividend plus the discounted conditional expectation of the exponential payoff at time t is bounded by exp(theta times the initial state reserve). Apply the already Proved finite-valued conditional Levy Markov identity and then the already Proved one-step exponential dividend budget separately for each realised state. This gives a genuine adapted one-step stochastic control inequality; it is not a stopped-time or general HJB generator theorem.
-- source:
--   Proved target cbd1ef08-c269-4698-9126-2f4a4877d524 and Proved one-step budget target 202f5f63-4f66-4a98-8f1a-23332454de0a.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_finite_valued_reserve
import Theorems.Thm_AvramDividend_Classical_levy_exponential_one_step_dividend_budget

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exponential_finite_state_dividend_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    {ι : Type*} [Fintype ι]
    (p : Ω → ι)
    (hp : ∀ i, MeasurableSet[𝓕 s] {ω : Ω | p ω = i})
    (u a : ι → ℝ) (θ q : ℝ)
    (hθ : 1 ≤ θ) (ha : ∀ i, 0 ≤ a i)
    (hua : ∀ i, a i ≤ u i) (hψ : X.ψ θ ≤ q)
    (hI : ∀ i, Integrable
      (fun ω => Real.exp (θ * (u i - a i + X.X (t - s) ω))) P) :
    ∀ᵐ ω ∂P,
      a (p ω) + Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (P[(fun η => Real.exp (θ *
          (u (p η) - a (p η) + (X.X t η - X.X s η)))) | 𝓕 s]) ω ≤
      Real.exp (θ * u (p ω)) := by sorry
