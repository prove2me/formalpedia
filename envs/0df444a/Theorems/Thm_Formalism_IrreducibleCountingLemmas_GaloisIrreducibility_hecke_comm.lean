-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_hecke_comm
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.hecke_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:44:08.40079+00:00
-- url     : https://prove2.me/theorems/f38773a0-e87e-4a11-b627-de78a35bdb85
-- title:
--   Galois Irreducibility: hecke comm
-- statement:
--   The Galois Irreducibility construction uses the hecke comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L90-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/MemBesselSetZeroIffUpperTriangular.lean#L90-L127

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

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.hecke_comm (σ : G → G) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (hσσ : ∀ x, σ (σ x) = x)
    (J : Subgroup G) (χ : J →* ℂˣ) (hJ : ∀ u : J, ∃ h : σ u ∈ J, χ ⟨σ u, h⟩ = χ u)
    (H : ∀ g, (∃ u u' : J, σ g = u * g * u' ∧ χ u * χ u' = 1) ∨
      (∃ u u' : J, (u : G) * g * u' = g ∧ χ u * χ u' ≠ 1)) (g g' : G) :
    (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) =
      (twistedIdem J χ * MonoidAlgebra.of ℂ G g' * twistedIdem J χ) *
        (twistedIdem J χ * MonoidAlgebra.of ℂ G g * twistedIdem J χ) := by sorry
