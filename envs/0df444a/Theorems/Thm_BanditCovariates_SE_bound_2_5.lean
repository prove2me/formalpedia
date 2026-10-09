-- Prove2me | Theorems.Thm_BanditCovariates_SE_bound_2_5
-- name    : BanditCovariates.SE.bound_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:05.483141+00:00
-- url     : https://prove2.me/theorems/0c205dfb-a16c-4d02-b902-d102b396d2b7
-- title:
--   Equation (2.5), p. 8 — empirical gap lower tail
-- statement:
--   In the sorted $K+1$ arm model, let $i$ be a suboptimal arm with gap $\Delta_i=f^*-f_i$. Let $\widehat\Delta_i(\tau)$ be the difference of the empirical means of the best arm and arm $i$ after $\tau\ge1$ samples each. If $\gamma U(\tau,T)\le\Delta_i$, then
--
--   $$P\{\widehat\Delta_i(\tau)<\gamma U(\tau,T)\}\le\exp\!\left(-\frac{\tau(\Delta_i-\gamma U(\tau,T))^2}{2}\right).$$
--
--   This lower-tail estimate controls failure to eliminate a sufficiently separated arm.
--
--   **Formalization Note** The printed phrase “for every $\tau\ge1$” needs the displayed threshold condition: a negative deviation size cannot be inserted into the stated Hoeffding bound. The proof uses the estimate where this condition holds. Rewards are bounded almost surely, and the published reward-stack model supplies independence.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 8, (2.5)

import Mathlib
import Definitions.Def_BanditCovariates_SE_Setting

namespace BanditCovariates.SE

open MeasureTheory ProbabilityTheory

/-- Equation (2.5), p. 8, in the range where the displayed Hoeffding estimate applies. -/
theorem bound_2_5 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (K : ℕ) (hK : 1 ≤ K)
    (Y : Fin (K + 1) → ℕ → Ω → ℝ) (f : Fin (K + 1) → ℝ)
    (hmodel : RegretBandits.Stochastic.IsStochasticBandit P Y f)
    (hbounded : ∀ i k, ∀ᵐ ω ∂P, Y i k ω ∈ Set.Icc (0 : ℝ) 1)
    (hordered : Monotone f)
    (hbest : ∀ i, i ≠ Fin.last K → f i < f (Fin.last K))
    (i : Fin (K + 1)) (hi : i ≠ Fin.last K)
    (T τ : ℕ) (hT : 1 ≤ T) (hτ : 1 ≤ τ) (γ : ℝ) (hγ : 1 ≤ γ)
    (hthreshold : γ * U τ T ≤ gap f i) :
    P.real {ω | estimatedGap Y i τ ω < γ * U τ T} ≤
      Real.exp (-(τ : ℝ) * (gap f i - γ * U τ T) ^ 2 / 2) := by sorry

end BanditCovariates.SE
