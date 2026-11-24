-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_pderiv_single_self
-- name    : Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.pderiv_single_self
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:38.988595+00:00
-- url     : https://prove2.me/theorems/826a0a50-9c26-44a9-a391-eea725f68789
-- title:
--   Gram Frame Composition Lin Facts: pderiv single self
-- statement:
--   The Gram Frame Composition Lin Facts construction uses the pderiv single self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L131-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L131-L134

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
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
open Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
open MvPowerSeries
variable {K : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.pderiv_single_self {τ : Type} (x : τ) (f : PowerSeries K) :
    pderiv K x (at1 x f) = at1 x (PowerSeries.derivative K f) := by sorry
