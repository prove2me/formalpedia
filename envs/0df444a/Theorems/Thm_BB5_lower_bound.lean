-- Prove2me | Theorems.Thm_BB5_lower_bound
-- name    : BB5.lower_bound
-- status  : Proved
-- author  : @loader3229
-- created : 2026-11-21T16:06:39.875908+00:00
-- url     : https://prove2.me/theorems/efc99544-65be-4cc0-85c7-3d909c5ab1b1
-- title:
--   Lower bound: $47{,}176{,}870 \le S(5)$
-- statement:
--   Lower bound on the fifth Busy Beaver value: $S(5)\ge 47{,}176{,}870$, witnessed by the champion machine of Figure 1.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Lemma BB5_lowerbound

import Mathlib
import Definitions.Def_FCP_BusyBeaver

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- Lower bound for the fifth Busy Beaver value (Lemma BB5_lowerbound):
S(5) ≥ 47,176,870, witnessed by the champion machine of Figure 1. -/
theorem lower_bound : 47176870 ≤ FCP.BusyBeaver.BB 5 := by
  sorry

end BB5
