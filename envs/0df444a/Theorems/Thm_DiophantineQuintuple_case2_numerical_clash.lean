-- Prove2me | Theorems.Thm_DiophantineQuintuple_case2_numerical_clash
-- name    : DiophantineQuintuple.case2_numerical_clash
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-23T15:42:12.594011+00:00
-- url     : https://prove2.me/theorems/e84f7ea0-3dcb-444f-a67a-7693bb69c054
-- title:
--   Numerical clash: 0.4553·b < n < h₂(b) forces b < 97000 (elementary)
-- statement:
--   Cipu-Fujita "Bounds for Diophantine quintuples", Glas. Mat. 50 (2015), p. 32: the index bounds 0.4553·b < n < h₂(b) force b < 97000. Elementary real analysis with numerical logarithm bounds (monotonicity plus endpoint estimates); tedious but not a deep blocker — the most attackable node of the case-2a≤b≤3a decomposition.
-- source:
--   Decomposition of diophantine_quintuple_not_b_le_3a_of_2a_le, Prove2Me There is no Diophantine quintuple mission

import Definitions.Def_diophantine_descent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false
open DiophantineDescent

namespace DiophantineQuintuple

theorem case2_numerical_clash (b n : Nat) (hb : 0 < b)
    (hlo : (0.4553:ℝ) * (b : ℝ) < (n : ℝ))
    (hhi : (n : ℝ) < 18 * Real.log (227.712 * (b : ℝ))
        * Real.log (1.976 * (b : ℝ))
        / (Real.log (1.908 * (b : ℝ)) * Real.log (1.007 : ℝ))) :
    b < 97000 := by sorry

end DiophantineQuintuple
