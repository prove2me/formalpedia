-- Prove2me | Theorems.Thm_Formalism_L2_Th1_B_ParE_subst_phE
-- name    : Formalism.L2.Th1.B.ParE.subst_phE
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:32.078174+00:00
-- url     : https://prove2.me/theorems/61d25145-633b-4f80-b669-9f7dcb9772f1
-- title:
--   Par E: subst ph E
-- statement:
--   The Par E construction uses the subst ph E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/WeierstrassSeriesIntegral.lean#L23-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/FrobeniusFibreCurves/LogarithmicSubstitution/WeierstrassSeriesIntegral.lean#L23-L38

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

theorem Formalism.L2.Th1.B.ParE.subst_phE (s2 e1 kap : K) (w : PowerSeries K) {l : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) {U : MvPowerSeries ι K}
    (hU : MvPowerSeries.constantCoeff U = 0) :
    PowerSeries.subst U (phE s2 e1 kap w l) =
      -PowerSeries.subst (PowerSeries.subst U l) (sigmaOneSeries e1 kap w) +
        MvPowerSeries.C (s2 / 2) * PowerSeries.subst U l ^ 2 := by sorry
