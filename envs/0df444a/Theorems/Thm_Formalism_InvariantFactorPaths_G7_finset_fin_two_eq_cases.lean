-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_finset_fin_two_eq_cases
-- name    : Formalism.InvariantFactorPaths.G7.finset_fin_two_eq_cases
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:58.30507+00:00
-- url     : https://prove2.me/theorems/6083d659-37a6-469d-a9e2-0cd29b7a216e
-- title:
--   G7: finset fin two eq cases
-- statement:
--   The G7 construction uses the finset fin two eq cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L228-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L228-L229

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
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

theorem Formalism.InvariantFactorPaths.G7.finset_fin_two_eq_cases : ∀ x y : Fin 2, x ≠ y → ∀ z, z = x ∨ z = y := by sorry
