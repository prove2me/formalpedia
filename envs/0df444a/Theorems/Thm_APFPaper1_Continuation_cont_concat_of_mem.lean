-- Prove2me | Theorems.Thm_APFPaper1_Continuation_cont_concat_of_mem
-- name    : APFPaper1.Continuation.cont_concat_of_mem
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:34:11.557037+00:00
-- url     : https://prove2.me/theorems/eca9017e-d969-46b0-a300-3d09800ababa
-- title:
--   A continuation can follow an executing word within the composite budget
-- statement:
--   Words are finite sequences of composable typed fragments, written in execution order. A supplied fragment relation determines relational execution. A supplied whole-word resource and calibration determine the bill; continuation membership requires an executing endpoint and a bill no greater than the capacity of the starting context. The theorem does not assume that w itself has already met a separate continuation-budget test. Suppose w executes from x to y, and u is a continuation from y in its own starting context. If the whole concatenation's bill fits w's starting-context capacity, then w followed by u is a continuation from x. Membership of u is used for an executing endpoint; its separate budget does not replace the composite budget. Source: Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.
-- source:
--   Theorems/Thm_APFPaper1_Cont_concatenation.lean, declaration at line 37 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.cont_concat_of_mem (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    {g h k : Context} (w : Word Frag g h) (u : Word Frag h k) (x : Raw g) (y : Raw h)
    (hw : Executes step w x y) (hu : Cont step resource calibration C h y ⟨k, u⟩)
    (hbudget : calibration g (resource g ⟨k, w.append u⟩) ≤ C g) :
    Cont step resource calibration C g x ⟨k, w.append u⟩ := by sorry
