-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvU_hop_mul_mem_span
-- name    : DiscreteGroups.sglob.LConvU.hop_mul_mem_span
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:52:48.480932+00:00
-- url     : https://prove2.me/theorems/57fc95c9-5356-49fd-acab-32988045e250
-- title:
--   LConv U: hop mul mem span
-- statement:
--   The LConv U construction uses the hop mul mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvUnifA.lean#L102-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvUnifA.lean#L102-L130

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

theorem DiscreteGroups.sglob.LConvU.hop_mul_mem_span (g h : G) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by sorry
