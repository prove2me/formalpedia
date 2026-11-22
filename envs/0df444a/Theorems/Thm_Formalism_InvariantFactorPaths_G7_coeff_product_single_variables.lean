-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_product_single_variables
-- name    : Formalism.InvariantFactorPaths.G7.coeff_product_single_variables
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:17.42682+00:00
-- url     : https://prove2.me/theorems/f8526b80-ca5e-4d8f-aa6e-28f9e59b7b32
-- title:
--   G7: coeff product single variables
-- statement:
--   The G7 construction uses the coeff product single variables property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L60-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L60-L88

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

theorem Formalism.InvariantFactorPaths.G7.coeff_product_single_variables {K ι : Type} [Field K] {x y : ι} (hxy : x ≠ y)
    (hall : ∀ z : ι, z = x ∨ z = y) (f g : PowerSeries K) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (at1 x f * at1 y g) =
      PowerSeries.coeff (n x) f * PowerSeries.coeff (n y) g := by sorry
