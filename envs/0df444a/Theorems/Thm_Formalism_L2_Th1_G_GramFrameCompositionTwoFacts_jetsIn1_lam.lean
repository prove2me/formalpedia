-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_GramFrameCompositionTwoFacts_jetsIn1_lam
-- name    : Formalism.L2.Th1.G.GramFrameCompositionTwoFacts.jetsIn1_lam
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:19:24.121675+00:00
-- url     : https://prove2.me/theorems/ffe474f4-c3dd-5f71-9a97-18596edcc83f
-- title:
--   Gram Frame Composition Two Facts: jets In1 lam
-- statement:
--   The Gram Frame Composition Two Facts construction uses the jets In1 lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ThetaZeroJetsCurveHolds.lean#L110-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ThetaZeroJetsCurveHolds.lean#L110-L133

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveSecondLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ThetaZeroJetsCurveHolds
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs

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
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.G.GramFrameCompositionTwoFacts.jetsIn1_lam {R : Subring K} (W : WeierstrassCurve K) (hW : CoeffIn R W) (x0 y0 s2 : K)
    (hE : W.toAffine.Equation x0 y0) (hx : x0 ∈ R) (hy : y0 ∈ R) (hs : x0 + W.b₂ / 12 + s2 ∈ R) :
    JetsIn1 R (lam (wTr W x0 y0) s2) := by sorry
