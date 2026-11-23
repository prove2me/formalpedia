-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_geom_sum_mul_pred
-- name    : Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.geom_sum_mul_pred
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:45.445806+00:00
-- url     : https://prove2.me/theorems/9a361bc6-5f4d-42be-babb-971a38c2aa79
-- title:
--   Logarithm Equivalence: geom sum mul pred
-- statement:
--   The Logarithm Equivalence construction uses the geom sum mul pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L235-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L235-L245

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

theorem Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.geom_sum_mul_pred {q : ℕ} (hq : 4 ≤ q) (j : ℕ) :
    ∃ g, q ^ j = (q - 1) * g + 1 ∧ j ≤ g ∧ (2 ≤ j → j + 1 ≤ g) := by sorry
