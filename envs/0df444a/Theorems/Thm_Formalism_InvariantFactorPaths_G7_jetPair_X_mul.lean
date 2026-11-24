-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_jetPair_X_mul
-- name    : Formalism.InvariantFactorPaths.G7.jetPair_X_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:55.131067+00:00
-- url     : https://prove2.me/theorems/d7cc9165-ae15-4686-9eb0-2e160fdcc960
-- title:
--   G7: jet Pair X mul
-- statement:
--   The G7 construction uses the jet Pair X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L135-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L135-L161

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FinsuppStepInduction
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
open Formalism.DworkPowerSeriesWeights (jetPair)
variable {K ι : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.jetPair_X_mul (Q : MvPolynomial ι K) (x : ι) (G : MvPowerSeries ι K) :
    jetPair Q (MvPowerSeries.X x * G) = jetPair (MvPolynomial.pderiv x Q) G := by sorry
