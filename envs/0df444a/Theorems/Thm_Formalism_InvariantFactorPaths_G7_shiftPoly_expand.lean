-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_shiftPoly_expand
-- name    : Formalism.InvariantFactorPaths.G7.shiftPoly_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:40.853663+00:00
-- url     : https://prove2.me/theorems/73b6bd3d-ede2-4d45-b3b9-ab0eef1791fb
-- title:
--   G7: shift Poly expand
-- statement:
--   The G7 construction uses the shift Poly expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L254-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L254-L258

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
variable {K ι κ : Type} [Field K] [Fintype κ]

theorem Formalism.InvariantFactorPaths.G7.shiftPoly_expand (b : κ → ι → K) (Q : MvPolynomial ι K) :
    shiftPoly b Q = ∑ d ∈ Q.support, MvPolynomial.C (MvPolynomial.C (MvPolynomial.coeff d Q)) *
      ∏ i ∈ d.support, shiftGen b i ^ d i := by sorry
