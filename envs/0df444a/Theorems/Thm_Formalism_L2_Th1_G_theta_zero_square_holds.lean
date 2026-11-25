-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_theta_zero_square_holds
-- name    : Formalism.L2.Th1.G.theta_zero_square_holds
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:09.815868+00:00
-- url     : https://prove2.me/theorems/27140906-a5b9-5dc4-9aba-d7ef79f45926
-- title:
--   G: theta zero square holds
-- statement:
--   The G construction uses the theta zero square holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ThetaZeroJetsCurveHolds.lean#L253-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ThetaZeroJetsCurveHolds.lean#L253-L269

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveSecondLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ThetaZeroJetsCurveHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xPlus)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)
open GramFrameCompositionTwoFacts

theorem Formalism.L2.Th1.G.theta_zero_square_holds : ThetaZeroSquare := by sorry
