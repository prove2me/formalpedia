-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_WeierstrassCurveSeries_subst_wTr
-- name    : Formalism.L2.Th1.C.WeierstrassCurveSeries.subst_wTr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:48:31.732548+00:00
-- url     : https://prove2.me/theorems/1880c02c-a759-5737-9142-3e6a8866c9cd
-- title:
--   Weierstrass Curve Series: subst w Tr
-- statement:
--   The Weierstrass Curve Series construction uses the subst w Tr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CurveIntegerMultiplicationSeries.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/CurveIntegerMultiplicationSeries.lean#L37-L44

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveEndoAll
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CubeThreeR
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_ChordEquation
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CurveIntegerMultiplicationSeries
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xS xPlus)
open Formalism.L2.Th1.C.WeierstrassCurveSeries
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.Th1.C.WeierstrassCurveSeries.subst_wTr (W : WeierstrassCurve K) (xP yP : K) :
    PowerSeries.subst (logSer W) (wTr W xP yP) = xPlus W xP yP + PowerSeries.C (W.b₂ / 12) := by sorry
