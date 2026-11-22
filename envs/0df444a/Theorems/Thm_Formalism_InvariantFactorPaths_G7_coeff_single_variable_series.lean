-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series
-- name    : Formalism.InvariantFactorPaths.G7.coeff_single_variable_series
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:30.041812+00:00
-- url     : https://prove2.me/theorems/351b5a8b-cf4e-4960-9657-9aa3ea2ed99c
-- title:
--   G7: coeff single variable series
-- statement:
--   The G7 construction uses the coeff single variable series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L43-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L43-L58

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

theorem Formalism.InvariantFactorPaths.G7.coeff_single_variable_series {K ι : Type} [Field K] [DecidableEq ι] (x : ι) (f : PowerSeries K)
    (n : ι →₀ ℕ) : MvPowerSeries.coeff n (at1 x f) =
      if n = Finsupp.single x (n x) then PowerSeries.coeff (n x) f else 0 := by sorry
