-- Prove2me | Theorems.Thm_CompanionTheory_FamInh_comap_connectedComponent
-- name    : CompanionTheory.FamInh.comap_connectedComponent
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:30:18.847454+00:00
-- url     : https://prove2.me/theorems/2033122d-8c5c-4143-aa95-6a06348b4e2e
-- title:
--   Fam Inh: comap connected Component
-- statement:
--   The Fam Inh construction uses the comap connected Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinKer.lean#L30-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/PlaceSeparation/ArtinKer.lean#L30-L85

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_CompanionTheory_AutomorphicTheory_PlaceSeparation_ArtinKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Topology GroundTheory.Global GroundTheory.Global.IdeleGroup
open CompanionTheory CompanionTheory.FamInh

theorem CompanionTheory.FamInh.comap_connectedComponent (E : Type) [Field E] [NumberField E] :
    (Subgroup.connectedComponentOfOne (GroundTheory.Global.IdeleClassGroup E)).comap (GroundTheory.Global.IdeleClassGroup.mk E) =
      ((Neutral.B1.diagUnits E).range ⊔ GlobalTheory.HeckeGal.infConn E).topologicalClosure := by sorry
