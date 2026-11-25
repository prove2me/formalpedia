-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_PairedSquareConstantCoefficients_inBlock_mul
-- name    : Formalism.L2.Th1.G.PairedSquareConstantCoefficients.inBlock_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:02:18.641449+00:00
-- url     : https://prove2.me/theorems/ec291448-eb3d-5ed9-bc47-16c99c5393ef
-- title:
--   Paired Square Constant Coefficients: in Block mul
-- statement:
--   The Paired Square Constant Coefficients construction uses the in Block mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ConstantCoeffCMulSqSum.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ConstantCoeffCMulSqSum.lean#L59-L61

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ConstantCoeffCMulSqSum
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
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.L2.Th1.G.PairedSquareConstantCoefficients
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.G.PairedSquareConstantCoefficients.inBlock_mul {ι B : Type} (k : B) (f g : MvPowerSeries ι K) :
    inBlock k (f * g) = inBlock k f * inBlock k g := by sorry
