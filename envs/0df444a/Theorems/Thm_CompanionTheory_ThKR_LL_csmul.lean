-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_LL_csmul
-- name    : CompanionTheory.ThKR.LL.csmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:08.993361+00:00
-- url     : https://prove2.me/theorems/ba834dd0-5fc5-4e55-801a-5ea318c5265a
-- title:
--   LL: csmul
-- statement:
--   The LL construction uses the csmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/HasDerivAtSchwartzToL2.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/HasDerivAtSchwartzToL2.lean#L18-L20

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaDef
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_HasDerivAtSchwartzToL2
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
open scoped Real
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]

theorem CompanionTheory.ThKR.LL.csmul (r : ℝ) (x : L2 l) : (r : ℂ) • x = r • x := by sorry
