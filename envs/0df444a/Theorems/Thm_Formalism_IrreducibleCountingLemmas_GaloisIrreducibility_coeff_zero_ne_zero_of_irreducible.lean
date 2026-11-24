-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_coeff_zero_ne_zero_of_irreducible
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.coeff_zero_ne_zero_of_irreducible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:31.662086+00:00
-- url     : https://prove2.me/theorems/42f601d2-9faf-40bc-b169-ffdefdb42d15
-- title:
--   Galois Irreducibility: coeff zero ne zero of irreducible
-- statement:
--   The Galois Irreducibility construction uses the coeff zero ne zero of irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CoeffZeroNeZeroOfIrreducible.lean#L68-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CoeffZeroNeZeroOfIrreducible.lean#L68-L76

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.coeff_zero_ne_zero_of_irreducible {f : K[X]} (hi : Irreducible f) (hd : 2 ≤ f.natDegree) :
    f.coeff 0 ≠ 0 := by sorry
