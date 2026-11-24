-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_norm_lamF_sub
-- name    : Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.norm_lamF_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:50.522823+00:00
-- url     : https://prove2.me/theorems/e342990a-dc41-4bf6-8dd4-390fb0166c89
-- title:
--   Logarithm Equivalence: norm lam F sub
-- statement:
--   The Logarithm Equivalence construction uses the norm lam F sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L247-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L247-L289

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

theorem Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.norm_lamF_sub {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {ϖ : K}
    (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K)) (n : ℕ) :
    ‖PowerSeries.coeff n (lamF p ϖ - PowerSeries.X - PowerSeries.X ^ (p ^ 2))‖ ≤ (p : ℝ)⁻¹ := by sorry
