-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_idem_sandwich
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.idem_sandwich
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:58.175012+00:00
-- url     : https://prove2.me/theorems/9f5aad29-949c-471e-91c2-e4fad1765c17
-- title:
--   Galois Irreducibility: idem sandwich
-- statement:
--   The Galois Irreducibility construction uses the idem sandwich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L25-L36

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.idem_sandwich (J : Subgroup G) (χ : J →* ℂˣ) (u u' : J) (g : G) :
    twistedIdem J χ * MonoidAlgebra.of ℂ G ((u : G) * g * u') * twistedIdem J χ =
      (((χ u * χ u' : ℂˣ)) : ℂ) •
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) := by sorry
