-- Prove2me | Theorems.Thm_BB5_finned4_nonhalting
-- name    : BB5.finned4_nonhalting
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T13:59:21.731797+00:00
-- url     : https://prove2.me/theorems/d28ddfbf-4cce-4647-94ba-aff15a768e4e
-- title:
--   Finned #4 does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Finned #4 never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. Holds three unary numbers while maintaining a linear relation; non-halting certified by a hand-crafted certificate (busycoq Finned4.v).
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Finned Machines

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Finned4

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Finned4

namespace BB5

/-- The sporadic machine Finned #4 (Section 5 - Finned Machines) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem finned4_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run finned4 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
