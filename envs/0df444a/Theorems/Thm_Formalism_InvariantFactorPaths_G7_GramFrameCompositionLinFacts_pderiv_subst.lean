-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_pderiv_subst
-- name    : Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.pderiv_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:48.078678+00:00
-- url     : https://prove2.me/theorems/7b25d8b6-9f27-4b33-932b-8207a9ab8cf7
-- title:
--   Gram Frame Composition Lin Facts: pderiv subst
-- statement:
--   The Gram Frame Composition Lin Facts construction uses the pderiv subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L34-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L34-L75

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

theorem Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.pderiv_subst {R σ τ : Type} [CommRing R] [Fintype σ] {a : σ → MvPowerSeries τ R}
    (ha : HasSubst a) (e : τ) (H : MvPowerSeries σ R) :
    pderiv R e (subst a H) = ∑ i, subst a (pderiv R i H) * pderiv R e (a i) := by sorry
