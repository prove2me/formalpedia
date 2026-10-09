-- Prove2me | Theorems.Thm_ActuarialValuation_finiteEntropicPremium_mono
-- name    : ActuarialValuation.finiteEntropicPremium_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T09:08:48.254454+00:00
-- url     : https://prove2.me/theorems/adfa89b1-90cc-4176-8c8b-19eb899e2bd8
-- title:
--   Positive-sensitivity exponential premium is monotone in loss
-- statement:
--   With strictly positive gamma and a nonnegative unit-sum weight vector, the entropic premium respects pointwise loss dominance.
--
--   **Mathematical statement**
--
--   $$
--   X\le Y,\gamma>0\implies\rho_\gamma(X)\le\rho_\gamma(Y)
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteEntropicPremium
open MeasureTheory

namespace ActuarialValuation

theorem finiteEntropicPremium_mono {Ω : Type*} [Fintype Ω] (w X Y : Ω → ℝ) (gamma : ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hsum : (∑ ω : Ω, w ω) = 1)
  (hgamma : 0 < gamma) (hXY : ∀ ω, X ω ≤ Y ω)
  :
  finiteEntropicPremium w X gamma ≤ finiteEntropicPremium w Y gamma := by sorry

end ActuarialValuation
