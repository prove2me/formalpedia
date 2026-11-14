-- Prove2me | Theorems.Thm_APFPaper1_Regulation_jointFraction_self
-- name    : APFPaper1.Regulation.jointFraction_self
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:35:26.722372+00:00
-- url     : https://prove2.me/theorems/c38069e4-3a00-4dc1-992f-629bcf29001a
-- title:
--   A holdable listed mark has self joint fraction one
-- statement:
--   Work in a supplied typed-word regulation model with a fragment execution relation, whole-word bills, starting-context capacities and Boolean readings on raw endpoint states. A mark is holdable when some budgeted response has a run reading it true; joint holdability requires both readings true in the same run. Without the listed holdable witness, the theorem does not assert self fraction one: the zero-denominator convention can instead give zero. Suppose a disturbance x₀ occurs in the supplied list and the mark m is holdable at x₀. Then the joint fraction of m with itself, computed on that list, is one. The witness makes the denominator positive, while self joint holdability and individual self holdability coincide at each listed disturbance. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_joint_fraction.lean, declaration at line 95 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

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

theorem APFPaper1.Regulation.jointFraction_self (g : Context) (xs : List (Raw g)) (m : M) (x0 : Raw g)
    (hx0 : x0 ∈ xs) (h : Holdable step resource calibration C reads g x0 m) :
    jointFraction step resource calibration C reads g xs m m = 1 := by sorry
