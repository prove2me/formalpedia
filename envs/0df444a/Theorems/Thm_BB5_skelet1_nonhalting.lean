-- Prove2me | Theorems.Thm_BB5_skelet1_nonhalting
-- name    : BB5.skelet1_nonhalting
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T13:46:59.123318+00:00
-- url     : https://prove2.me/theorems/c308805a-8414-4d58-9eca-7fa40521fa9c
-- title:
--   Skelet #1 does not halt
-- statement:
--   Started from the all-zero tape, the sporadic machine Skelet #1 never halts: for every number of steps t the run is still in a live (non-halted) configuration, i.e. it never reaches an undefined transition. Translated Cycler: after ~5.42×10^51 steps of chaos it enters an infinite translated loop (period > 8 billion); proved non-halting by Kądziołka in busycoq (Skelet1.v).
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Section 5 - Skelet #1 (Translated Cycler)

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet1

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_Skelet1

namespace BB5

/-- The sporadic machine Skelet #1 (Section 5 - Skelet #1 (Translated Cycler)) does not halt from the
all-zero tape: for every number of steps t the run is still in a live
(non-halted) configuration. Equivalently it never reaches an undefined
transition, so it never halts. -/
theorem skelet1_nonhalting :
    ∀ t : ℕ, FCP.BusyBeaver.run skelet1 (FCP.BusyBeaver.init (by omega)) t ≠ none := by
  sorry

end BB5
