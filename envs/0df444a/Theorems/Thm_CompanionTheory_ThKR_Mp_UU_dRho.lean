-- Prove2me | Theorems.Thm_CompanionTheory_ThKR_Mp_UU_dRho
-- name    : CompanionTheory.ThKR.Mp.UU_dRho
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:02.017321+00:00
-- url     : https://prove2.me/theorems/31b2dac9-ff40-402c-8047-a0d8beb68fb6
-- title:
--   Mp: UU d Rho
-- statement:
--   The Mp construction uses the UU d Rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L159-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/ThickeningEstimates/LieGroupReduction/MetaplecticRepresentation/MetaplecticUnipotentBlockSecondDiag.lean#L159-L164

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_dRho

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]

theorem CompanionTheory.ThKR.Mp.UU_dRho {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (w : l ⊕ l → ℝ) (f : Sch l) :
    UU S t (dRho w f) = dRho (nn S t *ᵥ w) (UU S t f) := by sorry
