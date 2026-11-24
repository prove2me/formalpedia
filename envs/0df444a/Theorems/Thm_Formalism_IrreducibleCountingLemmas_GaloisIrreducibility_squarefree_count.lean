-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_squarefree_count
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.squarefree_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:24.54752+00:00
-- url     : https://prove2.me/theorems/01e1d039-3560-4f83-bf51-4c43d2a26394
-- title:
--   Galois Irreducibility: squarefree count
-- statement:
--   The Galois Irreducibility construction uses the squarefree count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRSquarefreeCount.lean#L78-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRSquarefreeCount.lean#L78-L213

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.squarefree_count : SquarefreeCount := by sorry
