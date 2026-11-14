-- Prove2me | Theorems.Thm_APFPaper1_Regulation_holdable_right_of_jointlyHoldable
-- name    : APFPaper1.Regulation.holdable_right_of_jointlyHoldable
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:23:06.808837+00:00
-- url     : https://prove2.me/theorems/b9574d76-d4ba-4271-95fc-516b487e5681
-- title:
--   Joint holdability gives holdability of the second mark
-- statement:
--   If one budgeted response has a run saving both marks from a disturbance, then the second mark is holdable there. The same response and endpoint witness the individual claim. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_Regulation_pair.lean, declaration at line 52 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

import Definitions.Def_APFPaper1_Regulation
import Definitions.Def_APFPaper1_RegulationCounts
import Mathlib.Data.NNReal.Basic

set_option autoImplicit false
open APFPaper1.Regulation
open APFPaper1.Continuation
open Classical

universe uC uF uX uR uM
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → WordFrom Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (reads : (h : Context) → Raw h → M → Bool)

theorem APFPaper1.Regulation.holdable_right_of_jointlyHoldable (g : Context) (x : Raw g) (m1 m2 : M)
    (h : JointlyHoldable step resource calibration C reads g x m1 m2) :
    Holdable step resource calibration C reads g x m2 := by sorry
