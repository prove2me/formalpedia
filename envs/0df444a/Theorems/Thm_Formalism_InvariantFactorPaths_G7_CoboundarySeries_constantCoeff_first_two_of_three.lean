-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_constantCoeff_first_two_of_three
-- name    : Formalism.InvariantFactorPaths.G7.CoboundarySeries.constantCoeff_first_two_of_three
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:05.432944+00:00
-- url     : https://prove2.me/theorems/9060fbfa-b96c-47cd-9b53-ed67eb035263
-- title:
--   Coboundary Series: constant Coeff first two of three
-- statement:
--   The Coboundary Series construction uses the constant Coeff first two of three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L24-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L24-L39

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffFirstTwoOfThree
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
open Formalism.InvariantFactorPaths.G7.CoboundarySeries
open MvPowerSeries
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.CoboundarySeries.constantCoeff_first_two_of_three {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0) :
    constantCoeff (in3 F) = 0 := by sorry
