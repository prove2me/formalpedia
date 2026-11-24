-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_continuous_pderiv
-- name    : Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.continuous_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:53.078391+00:00
-- url     : https://prove2.me/theorems/3bf8147a-2055-4eba-9aa0-b9087f5e0ce5
-- title:
--   Gram Frame Composition Lin Facts: continuous pderiv
-- statement:
--   The Gram Frame Composition Lin Facts construction uses the continuous pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L19-L30

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

theorem Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.continuous_pderiv {R τ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalSemiring R]
    (e : τ) :
    let := WithPiTopology.instTopologicalSpace (σ := τ) (R := R)
    Continuous (fun f : MvPowerSeries τ R => pderiv R e f) := by sorry
