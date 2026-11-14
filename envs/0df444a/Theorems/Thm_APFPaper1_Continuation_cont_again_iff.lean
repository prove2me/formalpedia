-- Prove2me | Theorems.Thm_APFPaper1_Continuation_cont_again_iff
-- name    : APFPaper1.Continuation.cont_again_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:49:12.353168+00:00
-- url     : https://prove2.me/theorems/32211ad1-eab3-42f1-9a58-2de5cf5ed389
-- title:
--   Admission of a repeated word unfolds into two executions and budget
-- statement:
--   For a typed word returning to its own context, the double word u followed by u is in Cont at x exactly when u executes to some intermediate state, executes again there, and the complete double word fits the initial context budget. Actual repeated execution and its bill bound remain conditions.
-- source:
--   Sib v44 Theorems/Thm_APFPaper1_Cont_step_again.lean:49

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation
end APFPaper1.Continuation
open APFPaper1.Continuation
universe uC uF uX uR

variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.cont_again_iff (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (u : Word Frag g g) :
    Cont step resource calibration C g x ⟨g, u.append u⟩ ↔
      (∃ y : Raw g, Executes step u x y ∧ ∃ z : Raw g, Executes step u y z) ∧
        calibration g (resource g ⟨g, u.append u⟩) ≤ C g := by sorry
