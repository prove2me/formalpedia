-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_cont_pick_small
-- name    : AvramDividend.Classical.p2m81_cont_pick_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T07:59:59.128927+00:00
-- url     : https://prove2.me/theorems/4b60123c-5fcb-456e-a9aa-82e8a9978260
-- title:
--   Right-continuity picks small positive scale value
-- statement:
--   If W is continuous on [0,oo) with W 0 = 0, then for every positive c there is a positive a with W a < c. Pure Mathlib helper E for parent fc6b315a: right-continuity at 0 gives convergence along nhdsWithin (Ioi 0) 0, so W is eventually below c; extract the point. Supplies the small-a choice in the Tauberian contradiction.
-- source:
--   Decomposition child E of fc6b315a. Pure Mathlib via ContinuousWithinAt and nhdsWithin; no project imports.

import Mathlib
open Filter Set Topology
noncomputable section

theorem AvramDividend.Classical.p2m81_cont_pick_small (W : ℝ → ℝ) (c : ℝ)
    (hCont : ContinuousOn W (Ici (0:ℝ))) (hW0 : W 0 = 0) (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ W a < c := by sorry
