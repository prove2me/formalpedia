-- Prove2me | Theorems.Thm_ActuarialValuation_finiteExponentialMoment_nonnegative
-- name    : ActuarialValuation.finiteExponentialMoment_nonnegative
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T08:55:40.480818+00:00
-- url     : https://prove2.me/theorems/d01547fd-87f4-43e7-83f5-70dc2938f32e
-- title:
--   Exponential moment nonnegative for nonnegative scenario weights
-- statement:
--   Every scenario exponential is strictly positive; multiplied by a nonnegative weight it is nonnegative, so its finite sum is nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   w_\omega\ge0\implies M_\gamma(X)\ge0
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteExponentialMoment
open MeasureTheory

namespace ActuarialValuation

theorem finiteExponentialMoment_nonnegative {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (gamma : ℝ)
  (hw : ∀ ω, 0 ≤ w ω)
  :
  0 ≤ finiteExponentialMoment w X gamma := by sorry

end ActuarialValuation
