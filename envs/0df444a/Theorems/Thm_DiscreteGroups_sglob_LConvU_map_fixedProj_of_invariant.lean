-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvU_map_fixedProj_of_invariant
-- name    : DiscreteGroups.sglob.LConvU.map_fixedProj_of_invariant
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:53:51.765171+00:00
-- url     : https://prove2.me/theorems/08ff8a0a-a825-457f-bd6d-aa28626979c4
-- title:
--   LConv U: map fixed Proj of invariant
-- statement:
--   The LConv U construction uses the map fixed Proj of invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvUnifA.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvUnifA.lean#L63-L70

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

theorem DiscreteGroups.sglob.LConvU.map_fixedProj_of_invariant {U : Type*} [AddCommGroup U] [Module ℂ U] (f : V →ₗ[ℂ] U)
    (v : V) (hf : ∀ k ∈ K, f (ρ k v) = f v) : f (fixedProj ρ hρ hKc hKo v : V) = f v := by sorry
