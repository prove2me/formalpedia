-- Prove2me | Theorems.Thm_APFPaper1_Continuation_cont_bill_le_capacity
-- name    : APFPaper1.Continuation.cont_bill_le_capacity
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T16:30:14.313758+00:00
-- url     : https://prove2.me/theorems/af6692e7-2bfc-499f-996d-b0abd841f755
-- title:
--   A continuation meets its whole-word capacity bound
-- statement:
--   Words are finite sequences of composable typed fragments, written in execution order. A supplied fragment relation determines relational execution. A supplied whole-word resource and calibration determine the bill; continuation membership requires an executing endpoint and a bill no greater than the capacity of the starting context. This concerns the corrected word representation. It does not establish coarse-graining closure, a physical realization of the supplied step relation, or an unstated resource law. If w belongs to the corrected continuation class from raw input x in context g, its calibrated whole-word resource is at most the capacity of g. This is the budget conjunct of continuation membership. It is labelled by definition of Cont, rather than as an independently derived physical bill bound. Source: Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.
-- source:
--   Theorems/Thm_APFPaper1_Cont_bill_bound.lean, declaration at line 23 (Sib v15; source-scoped review). Paper 1 Supplement v9.28, lines 1224–1241 and 3188–3230; November 12 whole-word continuation ruling.

import Definitions.Def_APFPaper1_ContinuationWords

set_option autoImplicit false
open APFPaper1.Continuation
universe uC uF uX uR
variable {Context : Type uC} {Frag : Context → Context → Type uF} {Raw : Context → Type uX}
  {R : Context → Type uR}

theorem APFPaper1.Continuation.cont_bill_le_capacity (step : (g h : Context) → Frag g h → Raw g → Raw h → Prop)
    (resource : (g : Context) → WordFrom Frag g → R g)
    (calibration : (g : Context) → R g → NNReal) (C : Context → NNReal)
    (g : Context) (x : Raw g) (w : WordFrom Frag g)
    (hw : Cont step resource calibration C g x w) : calibration g (resource g w) ≤ C g := by sorry
