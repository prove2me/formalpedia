-- Prove2me | Theorems.Thm_ActuarialValuation_finiteExponentialMoment_shift
-- name    : ActuarialValuation.finiteExponentialMoment_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:02:25.976487+00:00
-- url     : https://prove2.me/theorems/fc56fb7b-9fb6-4191-8a4a-439dbc917544
-- title:
--   Deterministic cash shift factorises exponential moment
-- statement:
--   A constant cash shift contributes a common exponential multiplier e^(gamma c) to the weighted sum.
--
--   **Mathematical statement**
--
--   $$
--   M_\gamma(X+c)=e^{\gamma c}M_\gamma(X)
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteExponentialMoment
open MeasureTheory

namespace ActuarialValuation

theorem finiteExponentialMoment_shift {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (gamma c : ℝ)
  :
  finiteExponentialMoment w (fun ω => X ω + c) gamma =
  Real.exp (gamma * c) * finiteExponentialMoment w X gamma := by sorry

end ActuarialValuation
