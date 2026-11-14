-- Prove2me | Theorems.Thm_APFPaper1_Continuation_cont_identity
-- name    : APFPaper1.Continuation.cont_identity
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:35:42.327736+00:00
-- url     : https://prove2.me/theorems/2855d405-e07c-4efe-84a0-52f22f689f18
-- title:
--   A zero-bill empty word is an identity continuation
-- statement:
--   Words are finite sequences of composable typed fragments, written in execution order. A supplied fragment relation determines relational execution. A supplied whole-word resource and calibration determine the bill; continuation membership requires an executing endpoint and a bill no greater than the capacity of the starting context. The zero-bill premise remains explicit; this theorem does not prove it for an arbitrary supplied resource function. Fix a context g and raw input x. If the empty word at g has zero calibrated bill, it belongs to the corrected continuation class from x. Moreover, for every raw state z in g, the empty word executes from x to z exactly when x equals z. Capacity is nonnegative because its type is nonnegative real. Source: Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.
-- source:
--   Theorems/Thm_APFPaper1_Cont_identity.lean, declaration at line 24 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.cont_identity (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g)
    (hnull : calibration g (resource g (nullWord g)) = 0) :
    Cont step resource calibration C g x (nullWord g) ∧
      ∀ z : Raw g, Executes step (Word.nil g) x z ↔ x = z := by sorry
