-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_GramFrameCompositionTwoFacts_negY_two
-- name    : Formalism.L2.Th1.G.GramFrameCompositionTwoFacts.negY_two
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:29:20.5498+00:00
-- url     : https://prove2.me/theorems/9d1c262d-8b83-58dc-81dc-46dcd1b904b6
-- title:
--   Gram Frame Composition Two Facts: neg Y two
-- statement:
--   The Gram Frame Composition Two Facts construction uses the neg Y two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ThetaZeroJetsCurveHolds.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ThetaZeroJetsCurveHolds.lean#L21-L24

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
open Formalism.L2.Th1.G.GramFrameCompositionTwoFacts

theorem Formalism.L2.Th1.G.GramFrameCompositionTwoFacts.negY_two {K : Type} [Field K] (W : WeierstrassCurve K) (x0 y0 : K)
    (h : 2 * y0 + W.a₁ * x0 + W.a₃ = 0) : W.toAffine.negY x0 y0 = y0 := by sorry
