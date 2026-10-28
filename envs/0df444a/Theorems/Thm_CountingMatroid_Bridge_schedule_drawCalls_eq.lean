-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_schedule_drawCalls_eq
-- name    : CountingMatroid.Bridge.schedule_drawCalls_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T19:28:35.14724+00:00
-- url     : https://prove2.me/theorems/0be541a4-dc67-4b56-bfb6-7e005b060174
-- title:
--   Exact draw-call count in the common-base schedule
-- statement:
--   For every ground size and valid accuracy/confidence input, the computed schedule s satisfies s.drawCalls = 3 s.L (s.restartCap + s.observations). This is an identity of the existing schedule fields, not a statement that actual random reads stay inside a sampled block. It exposes the polynomial expression used in the eager-sampling budget.
-- source:
--   Original bridge contribution, 2026-10-24, for the existing Prove2me mission Approximate counting of common bases of two matroids. Uses meelgroup/counting-matroid commit dd16a4628fdb095c58fe0f3dfd8e353c6e97443c and the already published CommonBasesFPRAS definition. Does not claim a concrete bit-machine realization.

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- The concrete schedule's draw count, without any tape-coverage assumption. -/
theorem CountingMatroid.Bridge.schedule_drawCalls_eq (n : ℕ) (p : InputParams) :
    let s := (Program.schedule n p).val
    s.drawCalls = 3 * s.L * (s.restartCap + s.observations) := by
  sorry
