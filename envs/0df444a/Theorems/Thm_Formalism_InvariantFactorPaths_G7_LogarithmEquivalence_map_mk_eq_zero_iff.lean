-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_map_mk_eq_zero_iff
-- name    : Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.map_mk_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:16.82004+00:00
-- url     : https://prove2.me/theorems/186c04d3-910d-42e6-a835-6681e74aeb61
-- title:
--   Logarithm Equivalence: map mk eq zero iff
-- statement:
--   The Logarithm Equivalence construction uses the map mk eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L400-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/LogarithmEquivalence.lean#L400-L408

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

theorem Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.map_mk_eq_zero_iff {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) (f : PowerSeries (ballRing K)) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : ballRing K)})) f = 0 ↔
      ∀ n, ‖PowerSeries.coeff n (PowerSeries.map (ballRing K).subtype f)‖ ≤ (p : ℝ)⁻¹ := by sorry
