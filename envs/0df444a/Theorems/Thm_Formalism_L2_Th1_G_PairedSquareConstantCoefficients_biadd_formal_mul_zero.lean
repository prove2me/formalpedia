-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_PairedSquareConstantCoefficients_biadd_formal_mul_zero
-- name    : Formalism.L2.Th1.G.PairedSquareConstantCoefficients.biadd_formal_mul_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:01.894443+00:00
-- url     : https://prove2.me/theorems/59ed1740-dc35-5805-9929-bb1fb454b051
-- title:
--   Paired Square Constant Coefficients: biadd formal mul zero
-- statement:
--   The Paired Square Constant Coefficients construction uses the biadd formal mul zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ConstantCoeffCMulSqSum.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ConstantCoeffCMulSqSum.lean#L31-L35

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

theorem Formalism.L2.Th1.G.PairedSquareConstantCoefficients.biadd_formal_mul_zero {l linv ph : PowerSeries K} (h : IsLogPair l linv)
    (hph : PowerSeries.constantCoeff ph = 0) {σ : Type} (x : MvPowerSeries σ K) {y : MvPowerSeries σ K}
    (hy : MvPowerSeries.constantCoeff y = 0) : be0 l linv ph (fmul l linv 0 x) y = 0 := by sorry
