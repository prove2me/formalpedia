-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_gelfand_trick
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.gelfand_trick
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:43:59.328023+00:00
-- url     : https://prove2.me/theorems/ab73e19d-67ca-4bc5-bf35-10d6ab5b7288
-- title:
--   Galois Irreducibility: gelfand trick
-- statement:
--   The Galois Irreducibility construction uses the gelfand trick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L129-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L129-L137

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.gelfand_trick {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (J : Subgroup G) (χ : J →* ℂˣ)
    (hcomm : ∀ g g' : G, (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) =
      (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ))
    (hirr : IsIrr ρ) :
    Module.finrank ℂ (eqvSpace ρ (fun u : J => (u : G)) (fun u => ((χ u : ℂˣ) : ℂ))) ≤ 1 := by sorry
