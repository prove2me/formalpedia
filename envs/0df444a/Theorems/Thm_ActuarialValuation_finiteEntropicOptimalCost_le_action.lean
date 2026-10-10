-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicOptimalCost_le_action
-- name    : ActuarialValuation.finiteEntropicOptimalCost_le_action
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:16:18.230621+00:00
-- url     : https://prove2.me/theorems/c15b0315-7427-49ea-b9e7-8efffde47936
-- title:
--   Finite optimal entropic retention cost dominates all choices
-- statement:
--   By definition of finite minimum, no selected menu retention can have combined entropic premium cost below the minimum.
--
--   **Mathematical statement**
--
--   $$
--   J^\star_\gamma\le J_\gamma(\alpha_a)
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteEntropicOptimalCost
import Definitions.Def_actuarial_finiteEntropicRetentionCost
open MeasureTheory

namespace ActuarialValuation

theorem finiteEntropicOptimalCost_le_action {Ω A : Type*} [Fintype Ω] [Fintype A] [Nonempty A] (w z : Ω → ℝ) (reinsurancePremium : ℝ → ℝ)
  (retention : A → ℝ) (gamma : ℝ) (a : A)
  :
  finiteEntropicOptimalCost w z reinsurancePremium retention gamma ≤
  finiteEntropicRetentionCost w z reinsurancePremium gamma (retention a) := by sorry

end ActuarialValuation
