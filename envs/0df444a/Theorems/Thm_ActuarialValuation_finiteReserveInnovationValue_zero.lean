-- Prove2me | Theorems.Thm_ActuarialValuation_finiteReserveInnovationValue_zero
-- name    : ActuarialValuation.finiteReserveInnovationValue_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:00:33.309812+00:00
-- url     : https://prove2.me/theorems/b34d8f2b-332e-4f63-a061-34a31cdfef87
-- title:
--   Empty-horizon risk innovation value
-- statement:
--   An empty sum of discounted annual mortality surprises is zero.
--
--   **Mathematical statement**
--
--   $$
--   Z_0=0
--   $$
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem, European Actuarial Journal 11 319-323, especially equations (1), (3)-(5), https://doi.org/10.1007/s13385-020-00256-9; Gerber (1997), Life Insurance Mathematics, third ed., Chapter 6 section 6.7, https://doi.org/10.1007/978-3-662-03460-6

import Mathlib
import Definitions.Def_actuarial_finiteReserveInnovationValue
open MeasureTheory

namespace ActuarialValuation

theorem finiteReserveInnovationValue_zero (K : ℕ) (v : ℝ) (benefit reserve q : ℕ → ℝ)
  :
  finiteReserveInnovationValue K 0 v benefit reserve q = 0 := by sorry

end ActuarialValuation
