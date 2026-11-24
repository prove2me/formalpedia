-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_excluded_count_bound
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.excluded_count_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:07.635518+00:00
-- url     : https://prove2.me/theorems/7cef8b26-9467-47ed-84ad-d3e3eec576c0
-- title:
--   Galois Irreducibility: excluded count bound
-- statement:
--   The Galois Irreducibility construction uses the excluded count bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRExcludedCount.lean#L112-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRExcludedCount.lean#L112-L193

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBCard
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRBBDivides
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRExcludedCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.excluded_count_bound : ExcludedCount := by sorry
