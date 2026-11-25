-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_GramFrameCompositionTwoFacts_toZ_mvExp
-- name    : Formalism.L2.Th1.G.GramFrameCompositionTwoFacts.toZ_mvExp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:19:46.256352+00:00
-- url     : https://prove2.me/theorems/11018d3d-6db2-5d96-98ed-5f34fedd5e23
-- title:
--   Gram Frame Composition Two Facts: to Z mv Exp
-- statement:
--   The Gram Frame Composition Two Facts construction uses the to Z mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ThetaZeroJetsCurveHolds.lean#L208-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ThetaZeroJetsCurveHolds.lean#L208-L211

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
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.G.GramFrameCompositionTwoFacts.toZ_mvExp [CharZero K] {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) {f : MvPowerSeries n K}
    (hf : MvPowerSeries.constantCoeff f = 0) : toZ linv (mvExp f) = mvExp (toZ linv f) := by sorry
