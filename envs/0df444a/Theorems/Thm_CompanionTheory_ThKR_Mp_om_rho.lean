-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_om_rho
-- name    : CompanionTheory.ThKR.Mp.om_rho
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:59.922293+00:00
-- url     : https://prove2.me/theorems/222a5cbc-8af1-408c-b1c5-d6fcb4248d9c
-- title:
--   Mp: om rho
-- statement:
--   The Mp construction uses the om rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousOm.lean#L99-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousOm.lean#L99-L99

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
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
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable (l : Type) [Fintype l] [DecidableEq l]
variable {l}

theorem CompanionTheory.ThKR.Mp.om_rho (g : G l) (w : l ⊕ l → ℝ) (f : L2 l) : om g (rho w f) = rho ((pr g).1 *ᵥ w) (om g f) := by sorry
