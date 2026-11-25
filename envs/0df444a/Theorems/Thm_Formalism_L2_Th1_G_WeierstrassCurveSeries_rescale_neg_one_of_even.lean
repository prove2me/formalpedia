-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_WeierstrassCurveSeries_rescale_neg_one_of_even
-- name    : Formalism.L2.Th1.G.WeierstrassCurveSeries.rescale_neg_one_of_even
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T06:10:52.348126+00:00
-- url     : https://prove2.me/theorems/8b819dd2-8017-4a9d-b709-a59ff2183d6e
-- title:
--   Weierstrass Curve Series: rescale neg one of even
-- statement:
--   The Weierstrass Curve Series construction uses the rescale neg one of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/CurveFormalFirstLevelHolds.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/CurveFormalFirstLevelHolds.lean#L17-L23

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveSecondLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_CurveFormalFirstLevelHolds
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)
open Formalism.G (unitBall)
open Formalism.L2.Th1.G.WeierstrassCurveSeries

theorem Formalism.L2.Th1.G.WeierstrassCurveSeries.rescale_neg_one_of_even {K : Type} [Field K] (e : PowerSeries K)
    (h : ∀ n : ℕ, Odd n → PowerSeries.coeff n e = 0) : PowerSeries.rescale (-1 : K) e = e := by sorry
