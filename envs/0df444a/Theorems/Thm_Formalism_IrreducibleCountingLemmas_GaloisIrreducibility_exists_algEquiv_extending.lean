-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_exists_algEquiv_extending
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:55.697187+00:00
-- url     : https://prove2.me/theorems/408b41fe-1996-4fd9-8eac-65099b0ac195
-- title:
--   Galois Irreducibility: exists alg Equiv extending
-- statement:
--   The Galois Irreducibility construction uses the exists alg Equiv extending property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/FixedByAutomorphismInField.lean#L5-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/FixedByAutomorphismInField.lean#L5-L35

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FixedByAutomorphismInField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.exists_algEquiv_extending {F E : Type} [Field F] [Field E] [Algebra F E] [IsAlgClosed E]
    (σ₀ : algebraicClosure F E ≃ₐ[F] algebraicClosure F E) :
    ∃ σ : E ≃ₐ[F] E, ∀ a : algebraicClosure F E, σ (a : E) = (σ₀ a : E) := by sorry
