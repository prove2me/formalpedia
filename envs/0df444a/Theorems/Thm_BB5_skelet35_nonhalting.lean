-- Prove2me | Theorems.Thm_BB5_skelet35_nonhalting
-- name    : BB5.skelet35_nonhalting
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T13:56:10.779968+00:00
-- url     : https://prove2.me/theorems/24bd845f-de88-41a2-be3c-59d8ec827f7c
-- title:
--   Skelet #35 (Shift Overflow Counter) does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Skelet #35 (Shift Overflow Counter) never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. Two independent binary counters; non-halting follows from the reset invariant that rules out an overflow during a reset phase.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Shift Overflow Counters

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet35

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet35

namespace BB5

/-- The sporadic machine Skelet #35 (Shift Overflow Counter) (Section 5 - Shift Overflow Counters) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem skelet35_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run skelet35 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
