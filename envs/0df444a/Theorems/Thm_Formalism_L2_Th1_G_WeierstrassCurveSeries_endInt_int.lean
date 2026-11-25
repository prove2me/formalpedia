-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_WeierstrassCurveSeries_endInt_int
-- name    : Formalism.L2.Th1.G.WeierstrassCurveSeries.endInt_int
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:03:07.970223+00:00
-- url     : https://prove2.me/theorems/a7e34c6b-2b95-506f-9b40-558a35cee3d8
-- title:
--   Weierstrass Curve Series: end Int int
-- statement:
--   The Weierstrass Curve Series construction uses the end Int int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/CurveFormalFirstLevelHolds.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/CurveFormalFirstLevelHolds.lean#L38-L48

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

theorem Formalism.L2.Th1.G.WeierstrassCurveSeries.endInt_int {K : Type} [Field K] (R : Subring K) (l linv : PowerSeries K)
    (hl : IsLogPair l linv) (hF : FGInt R l linv) (n : ℤ) : EndInt R l linv (n : K) := by sorry
