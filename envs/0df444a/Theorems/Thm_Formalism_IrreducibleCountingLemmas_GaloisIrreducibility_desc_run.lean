-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_desc_run
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.desc_run
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:12.564553+00:00
-- url     : https://prove2.me/theorems/8389221a-afb5-459d-aefe-c1b4c59ffab4
-- title:
--   Galois Irreducibility: desc run
-- statement:
--   The Galois Irreducibility construction uses the desc run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L311-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L311-L361

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.desc_run (τ : Equiv.Perm (Fin N))
    (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1) :
    ∀ d : ℕ, ∀ i j : Fin N, (j : ℕ) = i + d → τ j < τ i → ∀ m : Fin N, i ≤ m → m ≤ j →
      (τ m : ℕ) + m = τ i + i := by sorry
