-- Prove2me | Theorems.Thm_CompanionTheory_Rg_Fl_hasPI_of
-- name    : CompanionTheory.Rg.Fl.hasPI_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:04:31.022673+00:00
-- url     : https://prove2.me/theorems/8b1fc9cb-95c0-41f3-a28a-31303ff7be7a
-- title:
--   Fl: has PI of
-- statement:
--   The Fl construction uses the has PI of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/InhabitedFinite.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/InhabitedFinite.lean#L129-L135

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.D.gk.admitted (stdPoly)
open scoped InnerProductSpace
open CompanionTheory CompanionTheory.Rg CompanionTheory.Rg.Fl

theorem CompanionTheory.Rg.Fl.hasPI_of (h2 : StSimple) (h3 : StStar) (h4 : StHecke) (h5 : StMod) (h7 : StTransfer)
    {G : Type} [Group G] {K : Subgroup G} {d l : ℕ} (hp : IsHeckePair K) (hc : IsCartan K d l) (hs : IsSep K) :
    ∃ M, HasPI K M := by sorry
