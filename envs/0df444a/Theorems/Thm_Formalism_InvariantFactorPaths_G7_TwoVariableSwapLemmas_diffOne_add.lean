-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_diffOne_add
-- name    : Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.diffOne_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:00.817464+00:00
-- url     : https://prove2.me/theorems/b2e63787-352c-420b-9f3c-e85761564741
-- title:
--   Two Variable Swap Lemmas: diff One add
-- statement:
--   The Two Variable Swap Lemmas construction uses the diff One add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L202-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ScalingSwapLemmas.lean#L202-L206

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ScalingSwapLemmas
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
open Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas
open MvPowerSeries
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.diffOne_add {F : MvPowerSeries (Fin 2) K} (hF : constantCoeff F = 0)
    (H H' : MvPowerSeries (Fin 2) K) : d1 F (H + H') = d1 F H + d1 F H' := by sorry
