-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_of
-- name    : Formalism.InvariantFactorPaths.G7.coeff_g0F_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:50.492668+00:00
-- url     : https://prove2.me/theorems/b3fc60f3-db46-4bef-8ab4-c1252b96d6dd
-- title:
--   G7: coeff g0 F of
-- statement:
--   The G7 construction uses the coeff g0 F of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L163-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L163-L168

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

theorem Formalism.InvariantFactorPaths.G7.coeff_g0F_of (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) (j : ℕ) :
    PowerSeries.coeff (p * (p ^ 2) ^ j) (g0F K p) = ((p : K) ^ (j + 1))⁻¹ := by sorry
