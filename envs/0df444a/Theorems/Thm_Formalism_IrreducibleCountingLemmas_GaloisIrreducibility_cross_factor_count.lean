-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_cross_factor_count
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.cross_factor_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:37.144963+00:00
-- url     : https://prove2.me/theorems/a00dcbcb-f387-40d4-b231-afe1d5353fe9
-- title:
--   Galois Irreducibility: cross factor count
-- statement:
--   The Galois Irreducibility construction uses the cross factor count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CrossFactorCount.lean#L51-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CrossFactorCount.lean#L51-L102

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.cross_factor_count : CrossFactorCount := by sorry
