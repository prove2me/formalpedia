-- Prove2me | Theorems.Thm_BB5_finned2_nonhalting
-- name    : BB5.finned2_nonhalting
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T13:57:50.017817+00:00
-- url     : https://prove2.me/theorems/e88fb9e0-a09b-4f79-a670-ab98edb9932c
-- title:
--   Finned #2 does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Finned #2 never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. Holds three unary numbers while maintaining a linear relation; non-halting certified by a hand-crafted WFAR-like certificate (Blanchard / Kądziołka, busycoq Finned2.v).
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Finned Machines

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Finned2

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Finned2

namespace BB5

/-- The sporadic machine Finned #2 (Section 5 - Finned Machines) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem finned2_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run finned2 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
