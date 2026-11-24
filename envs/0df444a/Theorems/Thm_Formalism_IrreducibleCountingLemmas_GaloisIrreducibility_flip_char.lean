-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_flip_char
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.flip_char
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:14.490803+00:00
-- url     : https://prove2.me/theorems/c883ca94-e1a3-47b4-bf1f-5e4f3abc67fe
-- title:
--   Galois Irreducibility: flip char
-- statement:
--   The Galois Irreducibility construction uses the flip char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L789-L795
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L789-L795

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.flip_char (ψ₀ : AddChar K ℂ) (u : uniSub K N) :
    ∃ h : flipG (u : GL (Fin N) K) ∈ uniSub K N, uniChar ψ₀ N ⟨flipG u, h⟩ = uniChar ψ₀ N u := by sorry
