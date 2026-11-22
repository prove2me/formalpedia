-- Prove2me | Theorems.Thm_BB5_skelet33_nonhalting
-- name    : BB5.skelet33_nonhalting
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T13:54:24.372822+00:00
-- url     : https://prove2.me/theorems/53dc9c80-9e09-4e8b-bb61-9bec2df67b05
-- title:
--   Skelet #33 (Shift Overflow Counter) does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Skelet #33 (Shift Overflow Counter) never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. Two independent binary counters; non-halting follows from the reset invariant that rules out an overflow during a reset phase.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Shift Overflow Counters

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet33

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet33

namespace BB5

/-- The sporadic machine Skelet #33 (Shift Overflow Counter) (Section 5 - Shift Overflow Counters) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem skelet33_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run skelet33 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
