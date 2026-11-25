-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_iso_big
-- name    : CompanionTheory.ThKR.LL.iso_big
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:05.035457+00:00
-- url     : https://prove2.me/theorems/0ad12062-2635-40c1-956d-775eb68b4f47
-- title:
--   LL: iso big
-- statement:
--   The LL construction uses the iso big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L185-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/IsoOfIntegral.lean#L185-L187

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

theorem CompanionTheory.ThKR.LL.iso_big {Ai : Eu l →L[ℝ] Eu l} (h : IsUnit Ai) (B C : Eu l →L[ℝ] Eu l) {c : ℝ} (hc : c ^ 2 = |Ai.det|) :
    Iso (big Ai B C c) := by sorry
