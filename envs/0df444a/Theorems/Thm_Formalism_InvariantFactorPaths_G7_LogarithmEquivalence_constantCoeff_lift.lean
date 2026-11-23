-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_constantCoeff_lift
-- name    : Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:14.505827+00:00
-- url     : https://prove2.me/theorems/4d007b88-a260-4357-b6fb-36653361f268
-- title:
--   Logarithm Equivalence: constant Coeff lift
-- statement:
--   The Logarithm Equivalence construction uses the constant Coeff lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L48-L53

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

theorem Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.constantCoeff_lift {K ι : Type} [NormedField K] [IsUltrametricDist K]
    {f₀ : MvPowerSeries ι (ballRing K)} {c : ballRing K}
    (h : MvPowerSeries.constantCoeff (MvPowerSeries.map (ballRing K).subtype f₀) = c) :
    MvPowerSeries.constantCoeff f₀ = c := by sorry
