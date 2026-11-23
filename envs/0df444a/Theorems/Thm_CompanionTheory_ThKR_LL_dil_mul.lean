-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_dil_mul
-- name    : CompanionTheory.ThKR.LL.dil_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:00.864527+00:00
-- url     : https://prove2.me/theorems/4c26bd68-4555-44ad-a431-8f85fc665c05
-- title:
--   LL: dil mul
-- statement:
--   The LL construction uses the dil mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L102-L104

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

theorem CompanionTheory.ThKR.LL.dil_mul {A B : Eu l →L[ℝ] Eu l} (hA : IsUnit A) (hB : IsUnit B) : dil A * dil B = dil (B * A) := by sorry
