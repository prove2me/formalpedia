-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_desc_const
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.desc_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:40.018914+00:00
-- url     : https://prove2.me/theorems/bfe1ad71-205e-43c5-bb64-c20b0641d7c6
-- title:
--   Galois Irreducibility: desc const
-- statement:
--   The Galois Irreducibility construction uses the desc const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L441-L470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L441-L470

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
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {N : ℕ}

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.desc_const {α : Type} (τ : Equiv.Perm (Fin N))
    (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1) (t : Fin N → α)
    (ht : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → t i = t j) (i : Fin N) :
    t (τ i) = t i := by sorry
