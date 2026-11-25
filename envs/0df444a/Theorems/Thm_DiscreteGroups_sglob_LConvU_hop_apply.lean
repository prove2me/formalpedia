-- Prove2me | Theorems.Thm_DiscreteGroups_sglob_LConvU_hop_apply
-- name    : DiscreteGroups.sglob.LConvU.hop_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:52:51.592858+00:00
-- url     : https://prove2.me/theorems/25e514fe-43ec-4735-9d8b-b64d625f349d
-- title:
--   LConv U: hop apply
-- statement:
--   The LConv U construction uses the hop apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvUnifA.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/DiscreteGroups/GlobalIrreducibility/LConvUnifA.lean#L77-L78

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

theorem DiscreteGroups.sglob.LConvU.hop_apply (g : G) (w : fixedVectors ρ K) :
    hop ρ hρ hKc hKo g w = fixedProj ρ hρ hKc hKo (ρ g w) := by sorry
