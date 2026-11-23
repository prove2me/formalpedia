-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_isUnit_dil
-- name    : CompanionTheory.ThKR.LL.isUnit_dil
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:05.007576+00:00
-- url     : https://prove2.me/theorems/d28c1320-2cd1-4959-be61-a7ca0bd12588
-- title:
--   LL: is Unit dil
-- statement:
--   The LL construction uses the is Unit dil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L106-L109

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem CompanionTheory.ThKR.LL.isUnit_dil {B : Eu l →L[ℝ] Eu l} (h : IsUnit B) : IsUnit (dil B) := by sorry
