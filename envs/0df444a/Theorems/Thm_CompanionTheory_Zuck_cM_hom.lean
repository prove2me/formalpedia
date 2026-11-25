-- Prove2me | Theorems.Thm_CompanionTheory_Zuck_cM_hom
-- name    : CompanionTheory.Zuck.cM_hom
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:34.038441+00:00
-- url     : https://prove2.me/theorems/446781c7-da37-518b-b093-75e13f5a3cd2
-- title:
--   Zuck: c M hom
-- statement:
--   The Zuck construction uses the c M hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/MultOne.lean#L56-L62

import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_MultOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped Kronecker
noncomputable section
open CompanionTheory CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem CompanionTheory.Zuck.cM_hom (hM : MatHom) (b : Bool) (B : URep k r) :
    IsHom ((vr k r b).tens (vr k r (!b)), B) (one B) (mAct (cM _)) := by sorry
