-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_character_inv
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.character_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:12.230063+00:00
-- url     : https://prove2.me/theorems/0d5e3407-6b3c-4dbf-a4b2-5f85ff6f5fcd
-- title:
--   Galois Irreducibility: character inv
-- statement:
--   The Galois Irreducibility construction uses the character inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCentralIdemSelfAdjoint.lean#L15-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRCentralIdemSelfAdjoint.lean#L15-L66

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.character_inv {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = (starRingEnd ℂ) (ρ.character g) := by sorry
