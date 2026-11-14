-- Prove2me | Theorems.Thm_APFPaper1_Regulation_bothCount_eq_eachCount_of_none
-- name    : APFPaper1.Regulation.bothCount_eq_eachCount_of_none
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:22:40.710384+00:00
-- url     : https://prove2.me/theorems/7c0a3cdc-d847-4c0c-9008-935dda5b27b4
-- title:
--   Without a listed joint obstruction the two counts agree
-- statement:
--   Work in a supplied typed-word regulation model with a fragment execution relation, whole-word bills, starting-context capacities and Boolean readings on raw endpoint states. A mark is holdable when some budgeted response has a run reading it true; joint holdability requires both readings true in the same run. Counts retain list multiplicity. Equality alone does not make the joint fraction one, since both counts can vanish; the theorem asserts neither a positive witness nor a physical probability interpretation. Suppose no disturbance in the supplied list satisfies the regulation obstruction predicate: individual holdability of both marks with failure of joint holdability. Then the jointly-holdable and individually-holdable counts on that list are equal. The absence assumption concerns only listed disturbances, not every possible raw input. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_Regulation_pair.lean, declaration at line 82 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

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

theorem APFPaper1.Regulation.bothCount_eq_eachCount_of_none (g : Context) (xs : List (Raw g)) (m1 m2 : M)
    (hnone : ∀ x ∈ xs, ¬ IrreduciblyJointAt step resource calibration C reads g x m1 m2) :
    bothCount step resource calibration C reads g xs m1 m2 =
      eachCount step resource calibration C reads g xs m1 m2 := by sorry
