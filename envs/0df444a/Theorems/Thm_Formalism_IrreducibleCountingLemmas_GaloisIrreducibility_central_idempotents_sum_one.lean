-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_central_idempotents_sum_one
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_sum_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:30.387319+00:00
-- url     : https://prove2.me/theorems/cb3f63c3-56cf-4eac-931a-a8c7c5e472e4
-- title:
--   Galois Irreducibility: central idempotents sum one
-- statement:
--   The Galois Irreducibility construction uses the central idempotents sum one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CentralIdempotentsSumOne.lean#L76-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CentralIdempotentsSumOne.lean#L76-L144

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CentralIdempotentsSumOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open CISum
set_option backward.isDefEq.respectTransparency false

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_sum_one : CentralIdemSumOne := by sorry
