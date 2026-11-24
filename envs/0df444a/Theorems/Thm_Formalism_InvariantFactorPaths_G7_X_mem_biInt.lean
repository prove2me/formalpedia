-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_X_mem_biInt
-- name    : Formalism.InvariantFactorPaths.G7.X_mem_biInt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:37.913697+00:00
-- url     : https://prove2.me/theorems/0a7f2a80-3ad0-4d46-866a-c94e4cbacea8
-- title:
--   G7: X mem bi Int
-- statement:
--   The G7 construction uses the X mem bi Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L410-L417
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L410-L417

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
variable (K ι κ : Type) [NormedField K] [IsUltrametricDist K]
variable {K ι κ}

theorem Formalism.InvariantFactorPaths.G7.X_mem_biInt (k : κ) :
    (MvPolynomial.X k : MvPolynomial κ (MvPolynomial ι K)) ∈ biInt K ι κ := by sorry
