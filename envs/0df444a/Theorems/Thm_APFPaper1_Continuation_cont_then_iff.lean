-- Prove2me | Theorems.Thm_APFPaper1_Continuation_cont_then_iff
-- name    : APFPaper1.Continuation.cont_then_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:49:37.156984+00:00
-- url     : https://prove2.me/theorems/b52e2de1-c927-4cde-80b6-cbefcc9a6dec
-- title:
--   Admission of a typed concatenation unfolds into execution and budget
-- statement:
--   The typed concatenation v followed by u belongs to Cont at x exactly when v executes to an intermediate state, u executes from that state to some endpoint, and the calibrated resource of the whole concatenation is at most the starting context’s capacity. No sum-of-bills rule is assumed.
-- source:
--   Sib v44 Theorems/Thm_APFPaper1_Cont_step_again.lean:35

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation
end APFPaper1.Continuation
open APFPaper1.Continuation
universe uC uF uX uR

variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.cont_then_iff (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    {g h k : Context} (x : Raw g) (v : Word Frag g h) (u : Word Frag h k) :
    Cont step resource calibration C g x ⟨k, v.append u⟩ ↔
      (∃ y : Raw h, Executes step v x y ∧ ∃ z : Raw k, Executes step u y z) ∧
        calibration g (resource g ⟨k, v.append u⟩) ≤ C g := by sorry
