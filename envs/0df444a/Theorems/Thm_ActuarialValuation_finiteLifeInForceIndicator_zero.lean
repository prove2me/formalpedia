-- Prove2me | Theorems.Thm_ActuarialValuation_finiteLifeInForceIndicator_zero
-- name    : ActuarialValuation.finiteLifeInForceIndicator_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T08:56:57.720688+00:00
-- url     : https://prove2.me/theorems/a9a2b20c-fc6e-438c-8a6c-808a9e0dec49
-- title:
--   Policy in force at inception
-- statement:
--   Every curtate lifetime is at least zero, so the policy is in force at issue.
--
--   **Mathematical statement**
--
--   $$
--   S_0(K)=1
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteLifeInForceIndicator
open MeasureTheory

namespace ActuarialValuation

theorem finiteLifeInForceIndicator_zero (K : ℕ)
  :
  finiteLifeInForceIndicator K 0 = 1 := by sorry

end ActuarialValuation
