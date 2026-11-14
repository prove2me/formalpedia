-- Prove2me | Theorems.Thm_APFPaper1_Continuation_contHereditary_iff_cont
-- name    : APFPaper1.Continuation.contHereditary_iff_cont
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:38:26.873446+00:00
-- url     : https://prove2.me/theorems/2fabdeb6-37b7-4357-89d3-5310511b813b
-- title:
--   Prefix-monotone bills identify hereditary and whole-word continuations
-- statement:
--   Words are finite sequences of composable typed fragments, written in execution order. A supplied fragment relation determines relational execution. A supplied whole-word resource and calibration determine the bill; continuation membership requires an executing endpoint and a bill no greater than the capacity of the starting context. The equivalence is conditional on prefix monotonicity. It does not prove that monotonicity holds physically or that it is necessary for coincidence in every particular model. Assume prefix-monotone calibrated resource. For every context, raw input and word, hereditary continuation membership holds if and only if whole-word continuation membership holds. Hereditary membership tests the same starting-context budget on every initial segment; whole-word membership tests only the complete word. Both require an executing endpoint. Source: Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.
-- source:
--   Theorems/Thm_APFPaper1_Cont_prefix_restriction.lean, declaration at line 55 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}





/-! ### 5. Hereditary and whole-word classes -/

theorem APFPaper1.Continuation.contHereditary_iff_cont (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (hmono : PrefixMonotone resource calibration)
    (g : Context) (x : Raw g) (w : WordFrom Frag g) :
    ContHereditary step resource calibration C g x w ↔ Cont step resource calibration C g x w := by sorry
