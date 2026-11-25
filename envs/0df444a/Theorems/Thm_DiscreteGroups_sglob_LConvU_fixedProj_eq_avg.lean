-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvU_fixedProj_eq_avg
-- name    : DiscreteGroups.sglob.LConvU.fixedProj_eq_avg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:02:35.236466+00:00
-- url     : https://prove2.me/theorems/b96aaa4d-2389-43db-b04d-c722d8d5c31c
-- title:
--   LConv U: fixed Proj eq avg
-- statement:
--   The LConv U construction uses the fixed Proj eq avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvUnifA.lean#L19-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvUnifA.lean#L19-L61

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_ReciprocityTheory_BurnsideSurjectivity_Burnside
import Definitions.Def_Development_DiscreteGroups_GlobalIrreducibility_LConvUnifA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open DiscreteGroups DiscreteGroups.sglob DiscreteGroups.sglob.LConvU
open GroundTheory.Automorphic Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
include hρ hKc hKo

theorem DiscreteGroups.sglob.LConvU.fixedProj_eq_avg {L : Subgroup G} (hLK : L ≤ K) (hLo : IsOpen (L : Set G)) :
    ∃ (N : ℕ) (r : Fin N → G), 0 < N ∧ (∀ i, r i ∈ K) ∧
      ∀ v : V, v ∈ fixedVectors ρ L →
        (fixedProj ρ hρ hKc hKo v : V) = (N : ℂ)⁻¹ • ∑ i, ρ (r i) v := by sorry
