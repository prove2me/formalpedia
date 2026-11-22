-- Prove2me | Theorems.Thm_BB5_champion_halts
-- name    : BB5.champion_halts
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-21T16:06:11.903342+00:00
-- url     : https://prove2.me/theorems/ccef2f77-e365-42fb-b6a0-3ce4da7b682e
-- title:
--   Champion halts in 47,176,870 steps
-- statement:
--   The 5-state champion machine of Figure 1, started on the all-zero tape in the first state, halts after exactly $47{,}176{,}870$ steps, with the final halting transition included in the count.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Figure 1 and Section 2

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_winner

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_winner

namespace BB5

/-- The 5-state champion machine of Figure 1 (Marxen--Buntrock 1989), started
on the all-zero tape in state A, halts after exactly 47,176,870 steps, where the
step count includes the final halting transition (paper Section 2 convention). -/
theorem champion_halts :
    FCP.BusyBeaver.HaltsIn winner (FCP.BusyBeaver.init (by omega)) 47176870 := by
  sorry

end BB5
