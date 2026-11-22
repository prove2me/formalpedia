-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
-- name    : Formalism.InvariantFactorPaths.G7.coeff_lgF_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:08.381328+00:00
-- url     : https://prove2.me/theorems/2d0b2134-3f89-42b4-a79e-027b28ebbc1a
-- title:
--   G7: coeff lg F ne zero
-- statement:
--   The G7 construction uses the coeff lg F ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L152-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L152-L161

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

theorem Formalism.InvariantFactorPaths.G7.coeff_lgF_ne_zero {K : Type} [Field K] {p n : ℕ}
    (h : PowerSeries.coeff n (lgF K p) ≠ 0) : ∃ j, n = (p ^ 2) ^ j := by sorry
