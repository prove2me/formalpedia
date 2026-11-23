-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_isUnit_ph
-- name    : CompanionTheory.ThKR.LL.isUnit_ph
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:35.173725+00:00
-- url     : https://prove2.me/theorems/6568bddd-3cab-498b-ad0e-d92095b0f6c3
-- title:
--   LL: is Unit ph
-- statement:
--   The LL construction uses the is Unit ph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L73-L74

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

theorem CompanionTheory.ThKR.LL.isUnit_ph (S : Eu l →L[ℝ] Eu l) : IsUnit (ph S) := by sorry
