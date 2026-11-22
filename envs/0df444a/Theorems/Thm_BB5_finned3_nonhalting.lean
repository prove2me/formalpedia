-- Prove2me | Theorems.Thm_BB5_finned3_nonhalting
-- name    : BB5.finned3_nonhalting
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T13:58:35.525379+00:00
-- url     : https://prove2.me/theorems/31050093-b998-43c6-86d5-42d86f59c39f
-- title:
--   Finned #3 does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Finned #3 never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. Holds three unary numbers maintaining a linear relation; also known to be irregular. Non-halting certified in busycoq (Finned3.v).
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Finned Machines

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Finned3

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Finned3

namespace BB5

/-- The sporadic machine Finned #3 (Section 5 - Finned Machines) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem finned3_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run finned3 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
