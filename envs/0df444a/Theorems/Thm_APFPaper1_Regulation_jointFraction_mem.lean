-- Prove2me | Theorems.Thm_APFPaper1_Regulation_jointFraction_mem
-- name    : APFPaper1.Regulation.jointFraction_mem
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:35:06.177203+00:00
-- url     : https://prove2.me/theorems/e8f9830e-3879-4d53-aab0-f1cec2c239f7
-- title:
--   Every joint fraction lies between zero and one
-- statement:
--   Work in a supplied typed-word regulation model with a fragment execution relation, whole-word bills, starting-context capacities and Boolean readings on raw endpoint states. A mark is holdable when some budgeted response has a run reading it true; joint holdability requires both readings true in the same run. Counts are taken over occurrences in the supplied finite list, so repetitions are retained. The joint fraction is the real quotient of the jointly-holdable count by the individually-holdable count, with zero denominator giving zero. For any supplied context, finite disturbance list and pair of marks, the joint fraction is nonnegative and at most one. The numerator counts disturbances with one successful joint response; the denominator counts disturbances with individual saving responses for both marks. Joint success entails individual success, so the numerator cannot exceed the denominator. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_joint_fraction.lean, declaration at line 80 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

import Definitions.Def_APFPaper1_JointFraction
import Theorems.Thm_APFPaper1_Regulation_irreduciblyJointAt_iff_overflow
import Theorems.Thm_APFPaper1_Regulation_eachCount_pos_of_mem
import Theorems.Thm_APFPaper1_Regulation_count_ratio_strictly_between

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

theorem APFPaper1.Regulation.jointFraction_mem (g : Context) (xs : List (Raw g)) (m1 m2 : M) :
    0 ≤ jointFraction step resource calibration C reads g xs m1 m2 ∧
      jointFraction step resource calibration C reads g xs m1 m2 ≤ 1 := by sorry
