-- Prove2me | Theorems.Thm_APFPaper1_Regulation_jointFraction_eq_zero_of_exclusive
-- name    : APFPaper1.Regulation.jointFraction_eq_zero_of_exclusive
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:33:46.899724+00:00
-- url     : https://prove2.me/theorems/0c868ef5-eb89-4fd2-b656-55de18100d1f
-- title:
--   Exclusive readings force the joint fraction to vanish
-- statement:
--   Work in a supplied typed-word regulation model with a fragment execution relation, whole-word bills, starting-context capacities and Boolean readings on raw endpoint states. A mark is holdable when some budgeted response has a run reading it true; joint holdability requires both readings true in the same run. This identifies a limitation of the co-holdability ratio. It does not prove that a mark's self fraction is one without a listed holdable witness, or equate the ratio with a turn number or quantum transition probability. Assume that at every raw state of every context the two supplied marks do not both read true. Their joint fraction is zero for every context and every finite disturbance list. The conclusion holds whether the denominator is positive or zero because there can be no successful joint-response witness. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_joint_fraction_exclusive.lean, declaration at line 52 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

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

theorem APFPaper1.Regulation.jointFraction_eq_zero_of_exclusive (m1 m2 : M)
    (hexcl : ∀ (h : Context) (y : Raw h), ¬ (reads h y m1 = true ∧ reads h y m2 = true))
    (g : Context) (xs : List (Raw g)) :
    jointFraction step resource calibration C reads g xs m1 m2 = 0 := by sorry
