-- Prove2me | Theorems.Thm_BB5_finned1_nonhalting
-- name    : BB5.finned1_nonhalting
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T13:56:59.989953+00:00
-- url     : https://prove2.me/theorems/ecbdaefd-24d1-424e-97e4-0584d06562a6
-- title:
--   Finned #1 does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Finned #1 never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. Holds three unary numbers on the tape, merging the middle into a neighbour while preserving a linear relation; any deviation would halt, so it never halts.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Finned Machines

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Finned1

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Finned1

namespace BB5

/-- The sporadic machine Finned #1 (Section 5 - Finned Machines) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem finned1_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run finned1 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
