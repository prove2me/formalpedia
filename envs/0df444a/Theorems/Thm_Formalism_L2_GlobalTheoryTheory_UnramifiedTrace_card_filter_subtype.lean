-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_UnramifiedTrace_card_filter_subtype
-- name    : Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_filter_subtype
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:14.127282+00:00
-- url     : https://prove2.me/theorems/ea214f7e-f5b9-4f8a-b518-c4d184f95e70
-- title:
--   Unramified Trace: card filter subtype
-- statement:
--   The Unramified Trace construction uses the card filter subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/CardFilterSubtype.lean#L151-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/CardFilterSubtype.lean#L151-L162

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
variable {K X : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [Fintype (Module.Dual K X)]

theorem Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_filter_subtype {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    [Fintype {a // p a}] :
    (Finset.univ.filter (fun a : {a // p a} => q a.1)).card = (Finset.univ.filter (fun a => p a ∧ q a)).card := by sorry
