-- Prove2me | Theorems.Thm_APFB06_step_taken_again_and_again
-- name    : APFB06.step_taken_again_and_again
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:14:46.31441+00:00
-- url     : https://prove2.me/theorems/eeb8092d-7e87-44d1-a283-d0c841ff9c71
-- title:
--   Step taken again and again
-- statement:
--   Assume the supplied selected protocol is admitted whenever the family is active and budgetAllows holds. If each iteration preserves the family, it is active initially, and budgetAllows holds along every iteration, then that protocol is admitted at every iterated state. The selection and instantiation rules are supplied, not derived from A2.
-- source:
--   Sib v44 Theorems/Thm_APFB04_steps_again.lean:78

import Definitions.Def_APF_B06_DeclaredInput
import Theorems.Thm_APFPaper5_K3_undo_is_a_repeat
import Theorems.Thm_APFPaper5_K3_kept_along_the_hold
import Theorems.Thm_APFPaper5_K3_every_state_comes_to_return
import Theorems.Thm_APFPaper5_K3_occupant_settles
import Theorems.Thm_APFPaper5_K3_finite_of_separating_family
import Theorems.Thm_APFB01_every_object_comes_to_return
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFB06.step_taken_again_and_again {Raw FullProcess : Type*}
    (Cont : Raw → FullProcess → Prop) (Dset : Set (APFB01.PhysicalState Cont → Bool))
    (protocols : Set FullProcess)
    (realized : Finset (APFB06.Task Cont Dset) → {p // p ∈ protocols})
    (budgetAllows : Finset (APFB06.Task Cont Dset) → Raw → Prop)
    (hinst : ∀ (S : Finset (APFB06.Task Cont Dset)) (x : Raw),
      (∀ d ∈ S, d.val (APFB01.physicalClass Cont x) = true) → budgetAllows S x →
        Cont x (realized S).val)
    (after : Raw → FullProcess → Raw) (S : Finset (APFB06.Task Cont Dset))
    (hkeepstep : ∀ y : Raw, (∀ d ∈ S, d.val (APFB01.physicalClass Cont y) = true) →
      ∀ d ∈ S, d.val (APFB01.physicalClass Cont (after y (realized S).val)) = true)
    (x : Raw) (hx : ∀ d ∈ S, d.val (APFB01.physicalClass Cont x) = true)
    (hbudget : ∀ n : ℕ, budgetAllows S ((fun y => after y (realized S).val)^[n] x)) (n : ℕ) :
    Cont ((fun y => after y (realized S).val)^[n] x) (realized S).val := by sorry
