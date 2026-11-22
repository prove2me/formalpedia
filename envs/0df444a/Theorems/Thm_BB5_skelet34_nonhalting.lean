-- Prove2me | Theorems.Thm_BB5_skelet34_nonhalting
-- name    : BB5.skelet34_nonhalting
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T13:55:20.925831+00:00
-- url     : https://prove2.me/theorems/ceadf0ab-a7d8-492e-babc-35ed9068bbc4
-- title:
--   Skelet #34 (Shift Overflow Counter) does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Skelet #34 (Shift Overflow Counter) never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. Two independent binary counters; first described informally by Ligocki, non-halting follows from the reset invariant.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Shift Overflow Counters

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet34

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet34

namespace BB5

/-- The sporadic machine Skelet #34 (Shift Overflow Counter) (Section 5 - Shift Overflow Counters) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem skelet34_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run skelet34 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
