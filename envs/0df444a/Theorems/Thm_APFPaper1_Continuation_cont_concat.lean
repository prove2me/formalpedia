-- Prove2me | Theorems.Thm_APFPaper1_Continuation_cont_concat
-- name    : APFPaper1.Continuation.cont_concat
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:32:38.785848+00:00
-- url     : https://prove2.me/theorems/f9a4fa44-0a99-4d7e-bc0d-0c06781edd60
-- title:
--   Executing words concatenate when the whole composite fits
-- statement:
--   Words are finite sequences of composable typed fragments, written in execution order. A supplied fragment relation determines relational execution. A supplied whole-word resource and calibration determine the bill; continuation membership requires an executing endpoint and a bill no greater than the capacity of the starting context. No hypothesis that either individual word is already a budgeted continuation is needed for this execution-shaped form. Suppose w executes from x to y and the matching word u executes from y to z. If the calibrated resource of w followed by u is at most the capacity of w's starting context, their concatenation is a continuation from x. The budget is on the actual complete word, not the sum of separately quoted bills. Source: Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.
-- source:
--   Theorems/Thm_APFPaper1_Cont_concatenation.lean, declaration at line 25 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.cont_concat (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    {g h k : Context} (w : Word Frag g h) (u : Word Frag h k) (x : Raw g) (y : Raw h) (z : Raw k)
    (hw : Executes step w x y) (hu : Executes step u y z)
    (hbudget : calibration g (resource g ⟨k, w.append u⟩) ≤ C g) :
    Cont step resource calibration C g x ⟨k, w.append u⟩ := by sorry
