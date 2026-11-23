-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_rhoFun_eq
-- name    : CompanionTheory.ThKR.LL.rhoFun_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:12.403961+00:00
-- url     : https://prove2.me/theorems/c24b2fcb-99e6-4455-86eb-55e3c853ae3d
-- title:
--   LL: rho Fun eq
-- statement:
--   The LL construction uses the rho Fun eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L17-L17

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

theorem CompanionTheory.ThKR.LL.rhoFun_eq (w : l ⊕ l → ℝ) (f : Eu l → ℂ) : rhoFun w f = rf (pPart w) (qPart w) f := by sorry
