-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_truncation_operator_holds
-- name    : Formalism.IrreducibleCountingLemmas.TW.truncation_operator_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:41.933027+00:00
-- url     : https://prove2.me/theorems/7f37ce1a-56a8-4ed7-a61c-af7c98e9b45d
-- title:
--   TW: truncation operator holds
-- statement:
--   The TW construction uses the truncation operator holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWCutOperator.lean#L13-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWCutOperator.lean#L13-L43

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWCentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWCutOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW

theorem Formalism.IrreducibleCountingLemmas.TW.truncation_operator_holds : CutOperator := by sorry
