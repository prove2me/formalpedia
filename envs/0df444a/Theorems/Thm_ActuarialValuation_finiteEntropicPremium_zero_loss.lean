-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicPremium_zero_loss
-- name    : ActuarialValuation.finiteEntropicPremium_zero_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T08:58:53.015797+00:00
-- url     : https://prove2.me/theorems/1de8baeb-45b6-4c39-ae91-d05509359872
-- title:
--   Zero loss has zero exponential premium
-- statement:
--   With unit scenario mass, the zero-loss exponential moment is one and its logarithm is zero; dividing by gamma yields zero even with Lean's totalised zero division.
--
--   **Mathematical statement**
--
--   $$
--   \rho_\gamma(0)=0
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteEntropicPremium
open MeasureTheory

namespace ActuarialValuation

theorem finiteEntropicPremium_zero_loss {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (gamma : ℝ)
  (hsum : (∑ ω : Ω, w ω) = 1)
  :
  finiteEntropicPremium w (fun _ => 0) gamma = 0 := by sorry

end ActuarialValuation
