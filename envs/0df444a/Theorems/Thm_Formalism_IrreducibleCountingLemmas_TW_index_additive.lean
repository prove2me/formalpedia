-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_index_additive
-- name    : Formalism.IrreducibleCountingLemmas.TW.index_additive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:07:27.213412+00:00
-- url     : https://prove2.me/theorems/009d0a58-3c2e-4e83-952d-7ab54c3c9666
-- title:
--   TW: index additive
-- statement:
--   The TW construction uses the index additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L224-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L224-L232

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW

theorem Formalism.IrreducibleCountingLemmas.TW.index_additive : IndexAdditive := by sorry
