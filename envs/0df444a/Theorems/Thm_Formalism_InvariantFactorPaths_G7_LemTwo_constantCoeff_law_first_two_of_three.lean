-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_constantCoeff_law_first_two_of_three
-- name    : Formalism.InvariantFactorPaths.G7.LemTwo.constantCoeff_law_first_two_of_three
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:11.538968+00:00
-- url     : https://prove2.me/theorems/5f196fbe-e8d1-4b43-9e87-4f9479ba3dc5
-- title:
--   Lem Two: constant Coeff law first two of three
-- statement:
--   The Lem Two construction uses the constant Coeff law first two of three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LemmaTwoOf.lean#L86-L88

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf
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
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.LemTwo.constantCoeff_law_first_two_of_three {g : MvPowerSeries (Fin 2) K} (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.constantCoeff (in3 g) = 0 := by sorry
