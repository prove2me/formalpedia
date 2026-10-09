-- Prove2me | Theorems.Thm_ActuarialValuation_compoundPoissonPanjerStep_one
-- name    : ActuarialValuation.compoundPoissonPanjerStep_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:33:16.4696+00:00
-- url     : https://prove2.me/theorems/2d78bef1-7e34-4bf6-8b76-ba6ae1fedb87
-- title:
--   First aggregate coefficient obeys the one-claim Panjer update
-- statement:
--   At aggregate loss exactly one, the only nonzero size-weighted severity term has claim size j=1. The update therefore equals the Poisson rate times the unit-claim severity probability times the zero-loss aggregate coefficient.
--
--   **Mathematical statement**
--
--   $$
--   P_\lambda(f,g;1)=\lambda f_1g_0
--   $$
-- source:
--   Harry H Panjer (1981), Recursive Evaluation of a Family of Compound Distributions, ASTIN Bulletin 12(1), 22–26, https://doi.org/10.1017/S0515036100006796; positive integer severity, compound Poisson specialisation

import Mathlib
import Definitions.Def_actuarial_compoundPoissonPanjerStep

namespace ActuarialValuation

theorem compoundPoissonPanjerStep_one
  (rate : ℝ) (f g : ℕ → ℝ) :
  compoundPoissonPanjerStep rate f g 1 = rate * f 1 * g 0 := by sorry

end ActuarialValuation
