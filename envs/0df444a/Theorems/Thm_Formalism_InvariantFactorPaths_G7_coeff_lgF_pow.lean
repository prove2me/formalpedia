-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow
-- name    : Formalism.InvariantFactorPaths.G7.coeff_lgF_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:38.028364+00:00
-- url     : https://prove2.me/theorems/78e833ea-183e-49ea-860f-0d36720682b9
-- title:
--   G7: coeff lg F pow
-- statement:
--   The G7 construction uses the coeff lg F pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L145-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L145-L150

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

theorem Formalism.InvariantFactorPaths.G7.coeff_lgF_pow (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    PowerSeries.coeff ((p ^ 2) ^ j) (lgF K p) = ((p : K) ^ j)⁻¹ := by sorry
