-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_idem_sandwich_zero
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.idem_sandwich_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:10.689802+00:00
-- url     : https://prove2.me/theorems/c7c63c46-c77e-435d-bdba-7c2d0cb33f28
-- title:
--   Galois Irreducibility: idem sandwich zero
-- statement:
--   The Galois Irreducibility construction uses the idem sandwich zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L38-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L38-L52

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.idem_sandwich_zero (J : Subgroup G) (χ : J →* ℂˣ) (u u' : J) (g : G)
    (h : (u : G) * g * u' = g) (hne : χ u * χ u' ≠ 1) :
    twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ = 0 := by sorry
