-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_norm_unif_pow
-- name    : Formalism.InvariantFactorPaths.G7.norm_unif_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:49.285802+00:00
-- url     : https://prove2.me/theorems/bcbdd55d-ba13-4d5a-bd35-4737d9ad8eba
-- title:
--   G7: norm unif pow
-- statement:
--   The G7 construction uses the norm unif pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MPlaces.lean#L19-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MPlaces.lean#L19-L35

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementM
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MPlaces
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul

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
open Formalism.DworkPowerSeriesWeights (Integral mvExp jetPair mfact)
open Formalism.FG.IntegralSubstitution (integral_mul integralSubstV)
open TwoS

theorem Formalism.InvariantFactorPaths.G7.norm_unif_pow {K : Type} [NormedField K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {ϖ : K} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K)) :
    ‖ϖ ^ (p + 1)‖ = (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by sorry
