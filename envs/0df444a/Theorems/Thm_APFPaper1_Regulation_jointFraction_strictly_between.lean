-- Prove2me | Theorems.Thm_APFPaper1_Regulation_jointFraction_strictly_between
-- name    : APFPaper1.Regulation.jointFraction_strictly_between
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:35:48.89933+00:00
-- url     : https://prove2.me/theorems/2e9c0649-1eb1-4671-b0f4-8845316e0b19
-- title:
--   A mixed disturbance list has joint fraction strictly between zero and one
-- statement:
--   Work in a supplied typed-word regulation model with a fragment execution relation, whole-word bills, starting-context capacities and Boolean readings on raw endpoint states. A mark is holdable when some budgeted response has a run reading it true; joint holdability requires both readings true in the same run. The theorem assumes these two kinds of disturbance exist; it does not derive either from B06 or assert that every real value in the interval occurs. Suppose the list contains x₀ where the pair is jointly holdable and x₁ where each mark is holdable but the pair is not jointly holdable. Then the joint fraction is strictly greater than zero and strictly smaller than one. Both witnesses must be members of the same supplied list. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_joint_fraction.lean, declaration at line 112 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

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

theorem APFPaper1.Regulation.jointFraction_strictly_between (g : Context) (xs : List (Raw g)) (m1 m2 : M)
    (x0 x1 : Raw g) (hx0 : x0 ∈ xs) (hx1 : x1 ∈ xs)
    (hheld : JointlyHoldable step resource calibration C reads g x0 m1 m2)
    (hirr : IrreduciblyJointAt step resource calibration C reads g x1 m1 m2) :
    0 < jointFraction step resource calibration C reads g xs m1 m2 ∧
      jointFraction step resource calibration C reads g xs m1 m2 < 1 := by sorry
