-- Prove2me | Theorems.Thm_Formalism_L2_Th1_G_PairedSquareConstantCoefficients_isPt_X
-- name    : Formalism.L2.Th1.G.PairedSquareConstantCoefficients.isPt_X
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:49:44.590389+00:00
-- url     : https://prove2.me/theorems/0c408720-3277-5f17-97d8-be9c085b7068
-- title:
--   Paired Square Constant Coefficients: is Pt X
-- statement:
--   The Paired Square Constant Coefficients construction uses the is Pt X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ConstantCoeffCMulSqSum.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/PairedSquareJets/ConstantCoeffCMulSqSum.lean#L23-L29

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_InverseEndoIntegralHolds
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversalLaw
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ConstantCoeffCMulSqSum
import Theorems.Thm_Formalism_L2_Th1_C_Pts_isPt_X

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

theorem Formalism.L2.Th1.G.PairedSquareConstantCoefficients.isPt_X (R : Subring K) {σ : Type} (a : σ) : IsPt R (MvPowerSeries.X a : MvPowerSeries σ K) := by sorry
