-- Prove2me | Theorems.Thm_BB5_skelet15_nonhalting
-- name    : BB5.skelet15_nonhalting
-- status  : Proved
-- author  : @loader3229
-- created : 2026-11-22T13:52:30.82194+00:00
-- url     : https://prove2.me/theorems/0d091ec1-5fd0-49a2-bcd1-0719284c7760
-- title:
--   Skelet #15 (Shift Overflow Counter) does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Skelet #15 (Shift Overflow Counter) never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. Two independent binary counters (left and right). An orderly counter phase alternates with a reset phase; the reset invariant prevents a second overflow, so it never halts.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Shift Overflow Counters

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet15

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet15

namespace BB5

/-- The sporadic machine Skelet #15 (Shift Overflow Counter) (Section 5 - Shift Overflow Counters) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem skelet15_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run skelet15 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
