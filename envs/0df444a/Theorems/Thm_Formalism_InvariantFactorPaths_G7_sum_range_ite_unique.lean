-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_sum_range_ite_unique
-- name    : Formalism.InvariantFactorPaths.G7.sum_range_ite_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:00.220921+00:00
-- url     : https://prove2.me/theorems/420e1173-6f03-45cb-b49b-28694a355f56
-- title:
--   G7: sum range ite unique
-- statement:
--   The G7 construction uses the sum range ite unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L135-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L135-L143

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

theorem Formalism.InvariantFactorPaths.G7.sum_range_ite_unique {M : Type} [AddCommMonoid M] (N : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (c : ℕ → M) (j0 : ℕ) (h0 : j0 < N) (hP : P j0) (hu : ∀ j, P j → j = j0) :
    (∑ j ∈ range N, if P j then c j else 0) = c j0 := by sorry
