-- Prove2me | Theorems.Thm_APFPaper1_Regulation_irreduciblyJointAt_iff_overflow
-- name    : APFPaper1.Regulation.irreduciblyJointAt_iff_overflow
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:29:40.679775+00:00
-- url     : https://prove2.me/theorems/bee5e171-5acd-48fb-b787-7ccc0c3005b2
-- title:
--   A joint obstruction is equivalent to a universal co-saving budget overflow
-- statement:
--   Work in a supplied typed-word regulation model with a fragment execution relation, whole-word bills, starting-context capacities and Boolean readings on raw endpoint states. A mark is holdable when some budgeted response has a run reading it true; joint holdability requires both readings true in the same run. The universal overflow condition may be vacuous if no co-saving executing run exists at any bill. The theorem therefore does not assert existence of an over-budget co-saving response. At a fixed disturbance, individual holdability of both marks together with failure of joint holdability is equivalent to individual holdability together with this condition: every word having an executing run ending with both marks true has bill strictly greater than the starting-context capacity. The same bill and reading data are used on both sides. Source: November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.
-- source:
--   Theorems/Thm_APFPaper1_Regulation_overflow.lean, declaration at line 34 (Sib v15; source-scoped review). November 12 regulation ruling; Paper 1 Supplement v9.28, lines 1224–1235, for the underlying continuation vocabulary.

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

theorem APFPaper1.Regulation.irreduciblyJointAt_iff_overflow (g : Context) (x : Raw g) (m1 m2 : M) :
    IrreduciblyJointAt step resource calibration C reads g x m1 m2 ↔
      Holdable step resource calibration C reads g x m1 ∧
      Holdable step resource calibration C reads g x m2 ∧
      ∀ w : WordFrom Frag g,
        (∃ y : Raw w.1, Executes step w.2 x y ∧ reads w.1 y m1 = true ∧ reads w.1 y m2 = true) →
          C g < calibration g (resource g w) := by sorry
