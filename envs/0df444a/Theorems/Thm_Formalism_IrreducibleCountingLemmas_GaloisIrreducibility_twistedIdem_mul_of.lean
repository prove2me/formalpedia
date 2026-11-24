-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_twistedIdem_mul_of
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem_mul_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:22.516577+00:00
-- url     : https://prove2.me/theorems/2b4223d8-c188-4161-81b8-384d6a8485ec
-- title:
--   Galois Irreducibility: twisted Idem mul of
-- statement:
--   The Galois Irreducibility construction uses the twisted Idem mul of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L13-L23

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
variable {G : Type} [Group G] [Fintype G]
open Classical

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem_mul_of (J : Subgroup G) (χ : J →* ℂˣ)
    (v : J) : twistedIdem J χ * MonoidAlgebra.of ℂ G (v : G)
      = ((χ v : ℂˣ) : ℂ) • twistedIdem J χ := by sorry
