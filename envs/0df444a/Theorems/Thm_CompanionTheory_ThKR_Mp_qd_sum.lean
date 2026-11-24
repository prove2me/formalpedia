-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_qd_sum
-- name    : CompanionTheory.ThKR.Mp.qd_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:08.873102+00:00
-- url     : https://prove2.me/theorems/cdf0cc90-8d75-459f-91cf-c880866a0456
-- title:
--   Mp: qd sum
-- statement:
--   The Mp construction uses the qd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MpFOne.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MpFOne.lean#L45-L52

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff RealInnerProductSpace
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]

theorem CompanionTheory.ThKR.Mp.qd_sum (X : Mat l) (f : Sch l) : ∑ a, ∑ b, X a b • Qd (Matrix.single a b 1) f = Qd X f := by sorry
