-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_ParE_subst_parallelogram_defect
-- name    : Formalism.L2.Th1.B.ParE.subst_parallelogram_defect
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:17.472828+00:00
-- url     : https://prove2.me/theorems/cba2a48b-385b-499d-899a-394e2d2ceb0b
-- title:
--   Par E: subst parallelogram defect
-- statement:
--   The Par E construction uses the subst parallelogram defect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/WeierstrassSeriesIntegral.lean#L47-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/WeierstrassSeriesIntegral.lean#L47-L69

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffSeriesAtVariable
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassSeriesIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_iff_lift
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_of_mul_eq_one
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_one__f427d3a2f5d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.ParE
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_iff_lift integral_mul' integral_one' integral_of_mul_eq_one)
variable {K : Type} [Field K] [CharZero K] {ι : Type}

theorem Formalism.L2.Th1.B.ParE.subst_parallelogram_defect (f : PowerSeries K) {U V : MvPowerSeries ι K}
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (par0 f) =
      PowerSeries.subst (U + V) f + PowerSeries.subst (U - V) f - 2 * PowerSeries.subst U f -
        2 * PowerSeries.subst V f := by sorry
