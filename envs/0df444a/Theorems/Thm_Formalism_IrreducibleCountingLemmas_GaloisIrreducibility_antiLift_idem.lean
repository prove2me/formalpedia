-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_antiLift_idem
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.antiLift_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:06.020807+00:00
-- url     : https://prove2.me/theorems/1f69dc11-da63-426e-bea5-37d91df2f6a8
-- title:
--   Galois Irreducibility: anti Lift idem
-- statement:
--   The Galois Irreducibility construction uses the anti Lift idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L73-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L73-L88

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.antiLift_idem (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσσ : ∀ x, σ (σ x) = x)
    (J : Subgroup G) (χ : J →* ℂˣ) (hJ : ∀ u : J, ∃ h : σ u ∈ J, χ ⟨σ u, h⟩ = χ u) :
    antiLift σ hσ (twistedIdem J χ) = MulOpposite.op (twistedIdem J χ) := by sorry
