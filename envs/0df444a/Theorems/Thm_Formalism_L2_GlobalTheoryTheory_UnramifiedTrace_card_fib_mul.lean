-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_UnramifiedTrace_card_fib_mul
-- name    : Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_fib_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:06.546159+00:00
-- url     : https://prove2.me/theorems/711be58d-b63c-4c49-b7bd-a489c781bbe7
-- title:
--   Unramified Trace: card fib mul
-- statement:
--   The Unramified Trace construction uses the card fib mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/CardFilterSubtype.lean#L17-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/CardFilterSubtype.lean#L17-L43

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_UnramifiedTrace_CardFilterSubtype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

theorem Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_fib_mul {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Fintype V] [Fintype W] [DecidableEq W] (f : V →+ W)
    (hf : Function.Surjective f) (w : W) :
    (Finset.univ.filter (fun v => f v = w)).card * Fintype.card W = Fintype.card V := by sorry
