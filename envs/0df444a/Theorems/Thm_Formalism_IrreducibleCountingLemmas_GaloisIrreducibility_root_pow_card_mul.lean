-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_root_pow_card_mul
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.root_pow_card_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:39.467447+00:00
-- url     : https://prove2.me/theorems/9b35bfb7-d4f7-4ed6-bc5c-b2d34cf87834
-- title:
--   Galois Irreducibility: root pow card mul
-- statement:
--   The Galois Irreducibility construction uses the root pow card mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CoeffZeroNeZeroOfIrreducible.lean#L56-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CoeffZeroNeZeroOfIrreducible.lean#L56-L61

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.root_pow_card_mul {f : K[X]} (hi : Irreducible f) {x : L} (hx : aeval x f = 0) (k : ℕ) :
    x ^ Fintype.card K ^ (f.natDegree * k) = x := by sorry
