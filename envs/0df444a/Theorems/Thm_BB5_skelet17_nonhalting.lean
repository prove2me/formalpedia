-- Prove2me | Theorems.Thm_BB5_skelet17_nonhalting
-- name    : BB5.skelet17_nonhalting
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T13:51:32.85481+00:00
-- url     : https://prove2.me/theorems/676d344f-52d2-4f3f-a97c-aa54d9e58d85
-- title:
--   Skelet #17 does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Skelet #17 never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. The last 5-state machine to be proved non-halting. Manages a unary-encoded list of naturals evolving by Gray-code-like transformations; it would halt only if n1=n2=0 and n3..nk all even, which never occurs.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Skelet #17 (last solved machine)

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet17

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet17

namespace BB5

/-- The sporadic machine Skelet #17 (Section 5 - Skelet #17 (last solved machine)) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem skelet17_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run skelet17 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
