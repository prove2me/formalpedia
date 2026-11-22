-- Prove2me | Theorems.Thm_BB5_finned5_nonhalting
-- name    : BB5.finned5_nonhalting
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T14:02:02.102954+00:00
-- url     : https://prove2.me/theorems/0bd43212-7903-4ad8-bcd1-d2cab789814a
-- title:
--   Finned #5 does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Finned #5 never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. Holds three unary numbers while maintaining a linear relation; non-halting certified by a hand-crafted certificate (busycoq Finned5.v).
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Finned Machines

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Finned5

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Finned5

namespace BB5

/-- The sporadic machine Finned #5 (Section 5 - Finned Machines) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem finned5_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run finned5 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
