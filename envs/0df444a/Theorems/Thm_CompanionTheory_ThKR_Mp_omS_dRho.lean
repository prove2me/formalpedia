-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_omS_dRho
-- name    : CompanionTheory.ThKR.Mp.omS_dRho
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:28.427889+00:00
-- url     : https://prove2.me/theorems/e957d44a-6c95-47ea-9830-d866d6a9d621
-- title:
--   Mp: om S d Rho
-- statement:
--   The Mp construction uses the om S d Rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousOm.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/ContinuousOm.lean#L101-L102

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_dRho
import Theorems.Thm_GlobalTheory_RealWeil_omS_dRho

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

theorem CompanionTheory.ThKR.Mp.omS_dRho (g : G l) (w : l ⊕ l → ℝ) (f : Sch l) : omS g (dRho w f) = dRho ((pr g).1 *ᵥ w) (omS g f) := by sorry
