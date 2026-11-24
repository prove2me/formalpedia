-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_include_three_zero
-- name    : Formalism.InvariantFactorPaths.G7.CoboundarySeries.include_three_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:26:05.568798+00:00
-- url     : https://prove2.me/theorems/78bfbbfc-f19b-4fed-9c1e-bb73bb96d49f
-- title:
--   Coboundary Series: include three zero
-- statement:
--   The Coboundary Series construction uses the include three zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffFirstTwoOfThree.lean#L98-L101

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

theorem Formalism.InvariantFactorPaths.G7.CoboundarySeries.include_three_zero : in3 (0 : MvPowerSeries (Fin 2) K) = 0 := by sorry
