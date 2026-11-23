-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_eq_of_common_root
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eq_of_common_root
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:03.525415+00:00
-- url     : https://prove2.me/theorems/450d7d01-996a-48bf-b8f7-cd73a294e9c8
-- title:
--   Galois Irreducibility: eq of common root
-- statement:
--   The Galois Irreducibility construction uses the eq of common root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CoeffZeroNeZeroOfIrreducible.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CoeffZeroNeZeroOfIrreducible.lean#L89-L94

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRFrobOrbitIrred
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSamePartCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eq_of_common_root {δ : ℕ} {a b : Fin δ → K} (ha : Irreducible (monicOf a))
    (hb : Irreducible (monicOf b)) {x : L} (hxa : aeval x (monicOf a) = 0)
    (hxb : aeval x (monicOf b) = 0) : a = b := by sorry
