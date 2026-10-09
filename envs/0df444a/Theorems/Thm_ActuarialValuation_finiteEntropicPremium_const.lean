-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicPremium_const
-- name    : ActuarialValuation.finiteEntropicPremium_const
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:01:49.793794+00:00
-- url     : https://prove2.me/theorems/9235b28d-75a3-49bf-b1ee-c05f0cf6bd4b
-- title:
--   Constant insurance loss premium equals the amount
-- statement:
--   At nonzero exponential sensitivity the logarithm of e^(gamma c) is gamma c, yielding certainty equivalent c.
--
--   **Mathematical statement**
--
--   $$
--   \gamma\ne0\implies\rho_\gamma(c)=c
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteEntropicPremium
open MeasureTheory

namespace ActuarialValuation

theorem finiteEntropicPremium_const {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (gamma c : ℝ)
  (hsum : (∑ ω : Ω, w ω) = 1) (hgamma : gamma ≠ 0)
  :
  finiteEntropicPremium w (fun _ => c) gamma = c := by sorry

end ActuarialValuation
