-- Prove2me | Theorems.Thm_BB5_skelet26_nonhalting
-- name    : BB5.skelet26_nonhalting
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T13:53:28.840804+00:00
-- url     : https://prove2.me/theorems/b33753e8-d2d0-4879-8848-19c5aecd3497
-- title:
--   Skelet #26 (Shift Overflow Counter) does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Skelet #26 (Shift Overflow Counter) never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. Two independent binary counters; the reset invariant maintained during each reset phase forbids the overflow that would cause a halt.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Shift Overflow Counters

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet26

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet26

namespace BB5

/-- The sporadic machine Skelet #26 (Shift Overflow Counter) (Section 5 - Shift Overflow Counters) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem skelet26_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run skelet26 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
