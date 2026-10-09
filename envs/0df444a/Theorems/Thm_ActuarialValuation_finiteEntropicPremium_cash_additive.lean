-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicPremium_cash_additive
-- name    : ActuarialValuation.finiteEntropicPremium_cash_additive
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:04:39.624309+00:00
-- url     : https://prove2.me/theorems/36a4d101-ada0-4f90-b768-d10e32c1d227
-- title:
--   Exponential premium is cash additive
-- statement:
--   Shifting every scenario loss by a fixed cash amount c shifts the certainty-equivalent exponential premium by exactly c when its logarithm is well-defined and gamma nonzero.
--
--   **Mathematical statement**
--
--   $$
--   \rho_\gamma(X+c)=\rho_\gamma(X)+c
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteEntropicPremium
import Definitions.Def_actuarial_finiteExponentialMoment
open MeasureTheory

namespace ActuarialValuation

theorem finiteEntropicPremium_cash_additive {Ω : Type*} [Fintype Ω] (w X : Ω → ℝ) (gamma c : ℝ)
  (hgamma : gamma ≠ 0)
  (hM : 0 < finiteExponentialMoment w X gamma)
  :
  finiteEntropicPremium w (fun ω => X ω + c) gamma =
  finiteEntropicPremium w X gamma + c := by sorry

end ActuarialValuation
