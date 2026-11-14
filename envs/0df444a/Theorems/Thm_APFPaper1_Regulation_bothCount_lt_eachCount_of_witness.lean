-- Prove2me | Theorems.Thm_APFPaper1_Regulation_bothCount_lt_eachCount_of_witness
-- name    : APFPaper1.Regulation.bothCount_lt_eachCount_of_witness
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:26:05.994984+00:00
-- url     : https://prove2.me/theorems/b56da935-8898-4c5b-9774-5faf7534cc6b
-- title:
--   One joint obstruction makes the two list counts differ strictly
-- statement:
--   Work in a supplied typed-word regulation model with a fragment execution relation, whole-word bills, starting-context capacities and Boolean readings on raw endpoint states. A mark is holdable when some budgeted response has a run reading it true; joint holdability requires both readings true in the same run. This proves strict comparison of counts; it does not assert a positive numerator, a specified numerical ratio or a physical score interpretation. Suppose x₀ occurs in the supplied disturbance list, each of the two marks is holdable at x₀, and they are not jointly holdable there. Then the jointly-holdable count on the list is strictly smaller than the individually-holdable count. No jointly-holdable witness elsewhere in the list is required for this strict inequality. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_Regulation_count_strict.lean, declaration at line 57 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

import Theorems.Thm_APFPaper1_Regulation_holdable_left_of_jointlyHoldable
import Theorems.Thm_APFPaper1_Regulation_holdable_right_of_jointlyHoldable
import Theorems.Thm_APFPaper1_Regulation_bothCount_le_eachCount
import Theorems.Thm_APFPaper1_Regulation_bothCount_eq_eachCount_of_none

set_option autoImplicit false
namespace APFPaper1.Regulation
end APFPaper1.Regulation
open APFPaper1.Regulation
open APFPaper1.Continuation
open Classical

universe uA uC uF uX uR uM



variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → WordFrom Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (reads : (h : Context) → Raw h → M → Bool)

theorem APFPaper1.Regulation.bothCount_lt_eachCount_of_witness (g : Context) (xs : List (Raw g)) (m1 m2 : M)
    (x0 : Raw g) (hx0 : x0 ∈ xs)
    (hirr : IrreduciblyJointAt step resource calibration C reads g x0 m1 m2) :
    bothCount step resource calibration C reads g xs m1 m2 <
      eachCount step resource calibration C reads g xs m1 m2 := by sorry
