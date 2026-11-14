-- Prove2me | Theorems.Thm_APFPaper1_Regulation_forced_choice_of_irreduciblyJointAt
-- name    : APFPaper1.Regulation.forced_choice_of_irreduciblyJointAt
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:26:15.122618+00:00
-- url     : https://prove2.me/theorems/4ea0753c-c95d-4da4-b5f2-b6da2690598e
-- title:
--   A joint obstruction excludes simultaneous survival on every budgeted run
-- statement:
--   Work in a supplied typed-word regulation model with a fragment execution relation, whole-word bills, starting-context capacities and Boolean readings on raw endpoint states. A mark is holdable when some budgeted response has a run reading it true; joint holdability requires both readings true in the same run. No choice rule selects which response occurs. No A2 minimum, BW uniqueness, probability, irreversible loss or inability to recover the second mark later is asserted. Assume that at a disturbance x each mark is holdable while the pair is not jointly holdable. Then there exists a budgeted saving response for the first mark and one for the second. Moreover, every executing run of every budgeted response from x that ends with the first mark true ends with the second false. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_Regulation_forced_choice.lean, declaration at line 30 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

import Theorems.Thm_APFPaper1_Regulation_holdable_left_of_jointlyHoldable
import Theorems.Thm_APFPaper1_Regulation_holdable_right_of_jointlyHoldable
import Theorems.Thm_APFPaper1_Regulation_bothCount_le_eachCount
import Theorems.Thm_APFPaper1_Regulation_bothCount_eq_eachCount_of_none

set_option autoImplicit false
namespace APFPaper1.Regulation
end APFPaper1.Regulation
open APFPaper1.Regulation
open APFPaper1.Continuation

universe uC uF uX uR uM
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR} {M : Type uM}
  (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
  (resource : (g : Context) → WordFrom Frag g → R g)
  (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
  (reads : (h : Context) → Raw h → M → Bool)

theorem APFPaper1.Regulation.forced_choice_of_irreduciblyJointAt (g : Context) (x : Raw g) (m1 m2 : M)
    (h : IrreduciblyJointAt step resource calibration C reads g x m1 m2) :
    (∃ w : WordFrom Frag g, Saves step resource calibration C reads g x w m1) ∧
    (∃ w : WordFrom Frag g, Saves step resource calibration C reads g x w m2) ∧
    ∀ (w : WordFrom Frag g) (y : Raw w.1), calibration g (resource g w) ≤ C g →
      Executes step w.2 x y → reads w.1 y m1 = true → reads w.1 y m2 = false := by sorry
