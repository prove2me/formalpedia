-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_antiLift_of
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.antiLift_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:18.277795+00:00
-- url     : https://prove2.me/theorems/ef088dcd-f155-457a-8cc0-e1fdd8f8be54
-- title:
--   Galois Irreducibility: anti Lift of
-- statement:
--   The Galois Irreducibility construction uses the anti Lift of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L68-L70

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.antiLift_of (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (g : G) :
    antiLift σ hσ (MonoidAlgebra.of ℂ G g) = MulOpposite.op (MonoidAlgebra.of ℂ G (σ g)) := by sorry
