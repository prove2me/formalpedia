-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_bruhat_step
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bruhat_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:31.0318+00:00
-- url     : https://prove2.me/theorems/f07341fa-9e95-46e3-92e7-9428359481f7
-- title:
--   Galois Irreducibility: bruhat step
-- statement:
--   The Galois Irreducibility construction uses the bruhat step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L541-L653
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L541-L653

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
open Classical

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bruhat_step (g : GL (Fin N) K) : ∀ k : ℕ, k ≤ N → ∃ u u' : GL (Fin N) K,
    IsUT (u : Matrix (Fin N) (Fin N) K) ∧ IsUT (u' : Matrix (Fin N) (Fin N) K) ∧
    ∃ p, Cleared ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) k p := by sorry
