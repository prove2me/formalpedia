-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
-- name    : Formalism.InvariantFactorPaths.G7.frobVar_eq_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:50:45.077897+00:00
-- url     : https://prove2.me/theorems/b2d35e66-e5d5-4db4-83d8-f6b97e3b6fc3
-- title:
--   G7: frob Var eq expand
-- statement:
--   The G7 construction uses the frob Var eq expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L14-L17

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

theorem Formalism.InvariantFactorPaths.G7.frobVar_eq_expand {K ι : Type} [Field K] {p : ℕ} (hp : p ≠ 0) (f : MvPowerSeries ι K) :
    frobVar p f = MvPowerSeries.expand p hp f := by sorry
