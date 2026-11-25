-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_local_estimate_second
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.local_estimate_second
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:16.476798+00:00
-- url     : https://prove2.me/theorems/cdcc4fd8-524e-4e36-9123-45532c730b8d
-- title:
--   Galois Irreducibility: local estimate second
-- statement:
--   The Galois Irreducibility construction uses the local estimate second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L429-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean#L429-L583

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.local_estimate_second : LocalEstimateII := by sorry
