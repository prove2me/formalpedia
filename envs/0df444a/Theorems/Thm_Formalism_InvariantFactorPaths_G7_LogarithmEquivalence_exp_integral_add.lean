-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_exp_integral_add
-- name    : Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.exp_integral_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:57.489803+00:00
-- url     : https://prove2.me/theorems/962603fd-8daf-45f6-bcf4-0fbe3845ab0c
-- title:
--   Logarithm Equivalence: exp integral add
-- statement:
--   The Logarithm Equivalence construction uses the exp integral add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L106-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L106-L113

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
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
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence

theorem Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.exp_integral_add {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
    {a b : MvPowerSeries ι K}
    (ha : MvPowerSeries.constantCoeff a = 0 ∧ Integral (mvExp a))
    (hb : MvPowerSeries.constantCoeff b = 0 ∧ Integral (mvExp b)) :
    MvPowerSeries.constantCoeff (a + b) = 0 ∧ Integral (mvExp (a + b)) := by sorry
