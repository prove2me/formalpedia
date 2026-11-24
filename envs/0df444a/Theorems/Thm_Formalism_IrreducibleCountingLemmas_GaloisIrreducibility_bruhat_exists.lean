-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_bruhat_exists
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bruhat_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:15.366572+00:00
-- url     : https://prove2.me/theorems/c632538a-59da-4ed4-b900-45d44f14b993
-- title:
--   Galois Irreducibility: bruhat exists
-- statement:
--   The Galois Irreducibility construction uses the bruhat exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L655-L675
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L655-L675

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.bruhat_exists (g : GL (Fin N) K) : ∃ u u' : GL (Fin N) K,
    IsUT (u : Matrix (Fin N) (Fin N) K) ∧ IsUT (u' : Matrix (Fin N) (Fin N) K) ∧
    ∃ (π : Equiv.Perm (Fin N)) (t : Fin N → K), (∀ j, t j ≠ 0) ∧
      ∀ i j, ((u * g * u' : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) i j =
        if i = π j then t j else 0 := by sorry
