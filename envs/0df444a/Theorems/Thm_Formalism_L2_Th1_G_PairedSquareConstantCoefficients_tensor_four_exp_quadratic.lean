-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_PairedSquareConstantCoefficients_tensor_four_exp_quadratic
-- name    : Formalism.L2.Th1.G.PairedSquareConstantCoefficients.tensor_four_exp_quadratic
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:31.533046+00:00
-- url     : https://prove2.me/theorems/55e726ff-9d26-5546-8a59-69d95dfb2a9a
-- title:
--   Paired Square Constant Coefficients: tensor four exp quadratic
-- statement:
--   The Paired Square Constant Coefficients construction uses the tensor four exp quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ConstantCoeffCMulSqSum.lean#L87-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ConstantCoeffCMulSqSum.lean#L87-L96

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
variable [CharZero K]

theorem Formalism.L2.Th1.G.PairedSquareConstantCoefficients.tensor_four_exp_quadratic {ι : Type} [Fintype ι] (s : K) (c : ι → K) :
    tens4 (mvExp (MvPowerSeries.C s * sqSum c)) =
      mvExp (MvPowerSeries.C s * sqSum (fun a : Fin 4 × ι => c a.2)) := by sorry
