-- Prove2me | Theorems.Thm_ActuarialValuation_finiteExponentialMoment_mono
-- name    : ActuarialValuation.finiteExponentialMoment_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:08:05.331983+00:00
-- url     : https://prove2.me/theorems/83cc7842-73ad-4326-80ce-99a126774bec
-- title:
--   Nonnegative weights preserve exponential moment ordering
-- statement:
--   Under nonnegative weights and gamma, exponentiation preserves order of the scenario losses, hence their weighted exponential sums are ordered.
--
--   **Mathematical statement**
--
--   $$
--   X\le Y,\gamma\ge0\implies M_\gamma(X)\le M_\gamma(Y)
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteExponentialMoment
open MeasureTheory

namespace ActuarialValuation

theorem finiteExponentialMoment_mono {Ω : Type*} [Fintype Ω] (w X Y : Ω → ℝ) (gamma : ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hgamma : 0 ≤ gamma)
  (hXY : ∀ ω, X ω ≤ Y ω)
  :
  finiteExponentialMoment w X gamma ≤ finiteExponentialMoment w Y gamma := by sorry

end ActuarialValuation
