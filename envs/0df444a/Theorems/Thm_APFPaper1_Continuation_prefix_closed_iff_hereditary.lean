-- Prove2me | Theorems.Thm_APFPaper1_Continuation_prefix_closed_iff_hereditary
-- name    : APFPaper1.Continuation.prefix_closed_iff_hereditary
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:40:04.531216+00:00
-- url     : https://prove2.me/theorems/eb300459-add8-46c5-9f16-c2c9ffdb205f
-- title:
--   Prefix closure is exactly coincidence with hereditary continuations
-- statement:
--   Words are finite sequences of composable typed fragments, written in execution order. A supplied fragment relation determines relational execution. A supplied whole-word resource and calibration determine the bill; continuation membership requires an executing endpoint and a bill no greater than the capacity of the starting context. This characterizes closure itself; it does not establish closure for arbitrary resources or claim that prefix monotonicity is necessary. The whole-word continuation class is closed under initial segments at every context and raw input if and only if, at every context and raw input, whole-word and hereditary membership agree for every word. Both sides refer to the same execution, resource, calibration and capacity data. No prefix-monotonicity premise is used in this characterization. Source: Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.
-- source:
--   Theorems/Thm_APFPaper1_Cont_prefix_restriction.lean, declaration at line 68 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}





/-! ### 5. Hereditary and whole-word classes -/

theorem APFPaper1.Continuation.prefix_closed_iff_hereditary (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal) :
    (∀ (g : Context) (x : Raw g) (v w : WordFrom Frag g), IsPrefix v w →
        Cont step resource calibration C g x w → Cont step resource calibration C g x v) ↔
    (∀ (g : Context) (x : Raw g) (w : WordFrom Frag g),
        Cont step resource calibration C g x w ↔ ContHereditary step resource calibration C g x w) := by sorry
