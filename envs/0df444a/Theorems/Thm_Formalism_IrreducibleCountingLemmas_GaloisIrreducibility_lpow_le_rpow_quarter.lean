-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_lpow_le_rpow_quarter
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.lpow_le_rpow_quarter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:58.556028+00:00
-- url     : https://prove2.me/theorems/e4f48b15-26fe-472c-95fe-e261e717f3c7
-- title:
--   Galois Irreducibility: lpow le rpow quarter
-- statement:
--   The Galois Irreducibility construction uses the lpow le rpow quarter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CoeffZeroNeZeroOfIrreducible.lean#L141-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/CoeffZeroNeZeroOfIrreducible.lean#L141-L150

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.lpow_le_rpow_quarter {l v g d : ℕ} (hBB : l ^ (4 * v) ≤ g ^ d) :
    ((l ^ v : ℕ) : ℝ) ≤ (g : ℝ) ^ ((d : ℝ) / 4) := by sorry
