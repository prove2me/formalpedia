-- Prove2me | Theorems.Thm_ActuarialValuation_finiteExponentialMoment_const
-- name    : ActuarialValuation.finiteExponentialMoment_const
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:01:26.455343+00:00
-- url     : https://prove2.me/theorems/30b19339-4e00-49d6-947d-79bee513b4f1
-- title:
--   Constant loss exponential moment
-- statement:
--   For a deterministic loss c the same exponential factor multiplies every scenario weight and unit mass leaves that factor unchanged.
--
--   **Mathematical statement**
--
--   $$
--   M_\gamma(c)=e^{\gamma c}
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteExponentialMoment
open MeasureTheory

namespace ActuarialValuation

theorem finiteExponentialMoment_const {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (gamma c : ℝ)
  (hsum : (∑ ω : Ω, w ω) = 1)
  :
  finiteExponentialMoment w (fun _ => c) gamma = Real.exp (gamma * c) := by sorry

end ActuarialValuation
