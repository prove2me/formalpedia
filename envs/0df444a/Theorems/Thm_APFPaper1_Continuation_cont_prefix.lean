-- Prove2me | Theorems.Thm_APFPaper1_Continuation_cont_prefix
-- name    : APFPaper1.Continuation.cont_prefix
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:37:13.978941+00:00
-- url     : https://prove2.me/theorems/9e677377-6aaa-47a4-8fc6-bd1140f7a69f
-- title:
--   Prefix-monotone bills give conditional prefix restriction
-- statement:
--   Words are finite sequences of composable typed fragments, written in execution order. A supplied fragment relation determines relational execution. A supplied whole-word resource and calibration determine the bill; continuation membership requires an executing endpoint and a bill no greater than the capacity of the starting context. The theorem preserves the same starting context, resource, calibration and capacity on the prefix and whole word. Assume calibrated whole-word resource is prefix-monotone: every initial segment has bill no greater than its whole word. Then every initial segment v of a continuation w from x is also a continuation from x. This is conditional C3, with prefix monotonicity named as a hypothesis rather than an adopted input or a consequence of Cont alone. Source: Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.
-- source:
--   Theorems/Thm_APFPaper1_Cont_prefix_restriction.lean, declaration at line 34 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.cont_prefix (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (hmono : PrefixMonotone resource calibration)
    (g : Context) (x : Raw g) (v w : WordFrom Frag g) (hpre : IsPrefix v w)
    (hw : Cont step resource calibration C g x w) :
    Cont step resource calibration C g x v := by sorry
