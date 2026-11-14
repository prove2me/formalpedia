-- Prove2me | Theorems.Thm_APFPaper1_Regulation_eachCount_pos_of_mem
-- name    : APFPaper1.Regulation.eachCount_pos_of_mem
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:29:23.863651+00:00
-- url     : https://prove2.me/theorems/7018be42-599b-4a9a-a665-825fa05619f4
-- title:
--   One listed jointly-held disturbance makes the individual count positive
-- statement:
--   If x₀ occurs in the list and one budgeted response has a run saving both marks there, then the count of listed disturbances where each mark is holdable is positive. Joint success supplies both individual witnesses. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_Regulation_overflow.lean, declaration at line 57 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

import Theorems.Thm_APFPaper1_Regulation_bothCount_lt_eachCount_of_witness

set_option autoImplicit false
namespace APFPaper1.Regulation
end APFPaper1.Regulation
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

theorem APFPaper1.Regulation.eachCount_pos_of_mem (g : Context) (xs : List (Raw g)) (m1 m2 : M) (x0 : Raw g)
    (hx0 : x0 ∈ xs) (hj : JointlyHoldable step resource calibration C reads g x0 m1 m2) :
    0 < eachCount step resource calibration C reads g xs m1 m2 := by sorry
