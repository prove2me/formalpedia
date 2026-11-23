-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_UnramifiedTrace_card_dual
-- name    : Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:05.651093+00:00
-- url     : https://prove2.me/theorems/578866da-cbe6-4e49-9408-caa58c13447c
-- title:
--   Unramified Trace: card dual
-- statement:
--   The Unramified Trace construction uses the card dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/CardFilterSubtype.lean#L57-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/UnramifiedTrace/CardFilterSubtype.lean#L57-L58

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

theorem Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.card_dual : Fintype.card (Module.Dual K X) = Fintype.card K ^ Module.finrank K X := by sorry
