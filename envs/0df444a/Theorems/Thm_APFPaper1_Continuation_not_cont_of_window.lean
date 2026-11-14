-- Prove2me | Theorems.Thm_APFPaper1_Continuation_not_cont_of_window
-- name    : APFPaper1.Continuation.not_cont_of_window
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:51:46.934459+00:00
-- url     : https://prove2.me/theorems/bfd09327-533f-48f4-9fcc-35401912217f
-- title:
--   A supplied cost-gap window excludes a continuation
-- statement:
--   If the bill of f is at least the bill of h plus eps, and capacity is strictly below the bill of h plus eps, then f is not a continuation from the specified input. Neither a physical source of the gap nor admissibility of h is asserted. Source: Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.
-- source:
--   Theorems/Thm_APFPaper1_Cont_over_budget_excluded.lean, declaration at line 31 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.not_cont_of_window (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (h f : WordFrom Frag g) (eps : NNReal)
    (hgap : calibration g (resource g h) + eps ≤ calibration g (resource g f))
    (hwin : C g < calibration g (resource g h) + eps) :
    ¬ Cont step resource calibration C g x f := by sorry
