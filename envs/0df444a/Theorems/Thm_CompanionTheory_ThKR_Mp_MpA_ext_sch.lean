-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_MpA_ext_sch
-- name    : CompanionTheory.ThKR.Mp.MpA.ext_sch
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:19:41.396793+00:00
-- url     : https://prove2.me/theorems/fe26247b-975e-4744-9113-6b295a5553a2
-- title:
--   Mp A: ext sch
-- statement:
--   The Mp A construction uses the ext sch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousTo.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousTo.lean#L22-L24

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousTo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
open CompanionTheory.ThKR.Mp.MpA

theorem CompanionTheory.ThKR.Mp.MpA.ext_sch (V : (Sch l →L[ℂ] Sch l)ˣ) (hn : ∀ f, ‖schwartzToL2 l (V.1 f)‖ = ‖schwartzToL2 l f‖) (f : Sch l) :
    ext V hn (schwartzToL2 l f) = schwartzToL2 l (V.1 f) := by sorry
