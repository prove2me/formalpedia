-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_hasseDir_mul
-- name    : Formalism.InvariantFactorPaths.G7.hasseDir_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:46.432181+00:00
-- url     : https://prove2.me/theorems/aaac91d5-89be-4df3-8342-08d8c3bf0d53
-- title:
--   G7: hasse Dir mul
-- statement:
--   The G7 construction uses the hasse Dir mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/FinsuppStepInduction.lean#L58-L61

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

theorem Formalism.InvariantFactorPaths.G7.hasseDir_mul [DecidableEq κ] (b : κ → ι → K) (β : κ →₀ ℕ) (f g : MvPolynomial ι K) :
    hasseDir b β (f * g) =
      ∑ x ∈ Finset.HasAntidiagonal.antidiagonal β, hasseDir b x.1 f * hasseDir b x.2 g := by sorry
