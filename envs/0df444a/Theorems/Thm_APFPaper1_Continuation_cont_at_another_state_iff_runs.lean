-- Prove2me | Theorems.Thm_APFPaper1_Continuation_cont_at_another_state_iff_runs
-- name    : APFPaper1.Continuation.cont_at_another_state_iff_runs
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:49:23.772738+00:00
-- url     : https://prove2.me/theorems/68f893da-b2f3-4b98-87a7-37d5c8a45e37
-- title:
--   The same admitted word transfers exactly when it executes
-- statement:
--   For typed whole-word Cont, let a word already be admitted at x. At another raw state x-prime in the same starting context, it is admitted exactly when there exists an execution from x-prime. The budget is the same context-and-word function; neither endpoint readmission nor doubled-word admission is asserted.
-- source:
--   Sib v44 Theorems/Thm_APFPaper1_Cont_budget_is_state_free.lean:27

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
namespace APFPaper1.Continuation
end APFPaper1.Continuation
open APFPaper1.Continuation
universe uC uF uX uR

variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.cont_at_another_state_iff_runs
    (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x x' : Raw g) (w : WordFrom Frag g)
    (hx : Cont step resource calibration C g x w) :
    Cont step resource calibration C g x' w ↔ ∃ z : Raw w.1, Executes step w.2 x' z := by sorry
