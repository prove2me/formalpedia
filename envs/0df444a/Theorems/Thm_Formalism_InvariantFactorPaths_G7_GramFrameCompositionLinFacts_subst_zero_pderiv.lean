-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_zero_pderiv
-- name    : Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.subst_zero_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:54.743987+00:00
-- url     : https://prove2.me/theorems/841b2c80-3a03-4d2a-bc9e-455b89f06c10
-- title:
--   Gram Frame Composition Lin Facts: subst zero pderiv
-- statement:
--   The Gram Frame Composition Lin Facts construction uses the subst zero pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L149-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/ConstantCoeffLawFirstTwoOfThree.lean#L149-L164

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

theorem Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.subst_zero_pderiv {τ : Type} (G : MvPowerSeries (Fin 2) K)
    {w : MvPowerSeries τ K} (hw : constantCoeff w = 0) :
    subst ![0, w] (pderiv K 0 G) = PowerSeries.subst w (fLin G) := by sorry
