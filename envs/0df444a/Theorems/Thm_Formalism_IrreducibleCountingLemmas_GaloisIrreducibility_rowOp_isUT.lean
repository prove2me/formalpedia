-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_rowOp_isUT
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.rowOp_isUT
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:30.522537+00:00
-- url     : https://prove2.me/theorems/43875972-07ce-49cd-9a58-05e2be09bd7a
-- title:
--   Galois Irreducibility: row Op is UT
-- statement:
--   The Galois Irreducibility construction uses the row Op is UT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L487-L500
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L487-L500

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K] {N : ℕ}

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.rowOp_isUT (a : Fin N → K) (r : Fin N) (ha : ∀ i, r ≤ i → a i = 0) :
    IsUT (rowOp a r) := by sorry
