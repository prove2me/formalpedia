-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_ph_mul
-- name    : CompanionTheory.ThKR.LL.ph_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:18:04.303981+00:00
-- url     : https://prove2.me/theorems/4bb8c326-2fcf-4762-9ecf-ac1c4fddbb41
-- title:
--   LL: ph mul
-- statement:
--   The LL construction uses the ph mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L61-L67

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

theorem CompanionTheory.ThKR.LL.ph_mul (S T : Eu l →L[ℝ] Eu l) : ph S * ph T = ph (S + T) := by sorry
