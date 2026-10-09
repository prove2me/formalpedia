-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicPremiumRetention_fundamental
-- name    : ActuarialValuation.finiteEntropicPremiumRetention_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:18:46.757315+00:00
-- url     : https://prove2.me/theorems/36771602-e7c7-4946-965e-2e0793432c82
-- title:
--   Finite entropic retention cost optimality and attained minimum
-- statement:
--   The finite entropic-risk-adjusted reinsurance cost is below or equal to the cost of any allowable retention and is attained by a chosen retention from the same nonempty finite menu.
--
--   **Mathematical statement**
--
--   $$
--   J^\star_\gamma=\min_{a\in A}[q(\alpha_a)+\rho_\gamma(r(Z,\alpha_a))]
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteEntropicOptimalCost
import Definitions.Def_actuarial_finiteEntropicRetentionCost
open MeasureTheory

namespace ActuarialValuation

theorem finiteEntropicPremiumRetention_fundamental {Ω A : Type*} [Fintype Ω] [Fintype A] [Nonempty A] (w z : Ω → ℝ) (reinsurancePremium : ℝ → ℝ)
  (retention : A → ℝ) (gamma : ℝ)
  :
  ((∀ a : A, finiteEntropicOptimalCost w z reinsurancePremium retention gamma ≤
  finiteEntropicRetentionCost w z reinsurancePremium gamma (retention a))
  ∧ (∃ a : A, finiteEntropicOptimalCost w z reinsurancePremium retention gamma =
    finiteEntropicRetentionCost w z reinsurancePremium gamma (retention a))) := by sorry

end ActuarialValuation
