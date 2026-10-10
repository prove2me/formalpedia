-- Prove2me | Theorems.Thm_ActuarialValuation_finiteExponentialMoment_zero_loss
-- name    : ActuarialValuation.finiteExponentialMoment_zero_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T08:58:13.241983+00:00
-- url     : https://prove2.me/theorems/30b58084-7d01-47cd-a155-1b7502d04625
-- title:
--   Zero loss gives a unit exponential moment
-- statement:
--   The exponential of zero is one in each scenario, so normalised scenario weights sum to the unit moment.
--
--   **Mathematical statement**
--
--   $$
--   M_\gamma(0)=1
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteExponentialMoment
open MeasureTheory

namespace ActuarialValuation

theorem finiteExponentialMoment_zero_loss {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (gamma : ℝ)
  (hsum : (∑ ω : Ω, w ω) = 1)
  :
  finiteExponentialMoment w (fun _ => 0) gamma = 1 := by sorry

end ActuarialValuation
