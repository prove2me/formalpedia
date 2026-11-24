-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_besselSet_zero_iff_upper_triangular
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_besselSet_zero_iff_upper_triangular
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:01.483325+00:00
-- url     : https://prove2.me/theorems/887ac483-b759-4db0-b09f-8c9275893ece
-- title:
--   Galois Irreducibility: mem bessel Set zero iff upper triangular
-- statement:
--   The Galois Irreducibility construction uses the mem bessel Set zero iff upper triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L155-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L155-L162

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_besselSet_zero_iff_upper_triangular (u : GL (Fin N) K) : u ∈ besselSet K 0 0 N ↔ IsUT (u : Matrix (Fin N) (Fin N) K) := by sorry
