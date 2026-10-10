-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicRetainedClaim_monotone
-- name    : ActuarialValuation.finiteEntropicRetainedClaim_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:15:03.109982+00:00
-- url     : https://prove2.me/theorems/776e1f2a-82bd-4244-8799-e228396ffde5
-- title:
--   Retained claims increase with retention
-- statement:
--   Increasing the insurer's retention threshold cannot reduce the claim it retains for any fixed gross claim.
--
--   **Mathematical statement**
--
--   $$
--   a\le b\implies r(z,a)\le r(z,b)
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteEntropicRetainedClaim
open MeasureTheory

namespace ActuarialValuation

theorem finiteEntropicRetainedClaim_monotone (z a b : ℝ) (hab : a ≤ b)
  :
  finiteEntropicRetainedClaim z a ≤ finiteEntropicRetainedClaim z b := by sorry

end ActuarialValuation
