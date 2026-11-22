-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ppowq_inj
-- name    : Formalism.InvariantFactorPaths.G7.ppowq_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:50:51.020936+00:00
-- url     : https://prove2.me/theorems/3c189b40-40fc-4850-9603-d49d6006c210
-- title:
--   G7: ppowq inj
-- statement:
--   The G7 construction uses the ppowq inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L113-L115

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

theorem Formalism.InvariantFactorPaths.G7.ppowq_inj {p : ℕ} (hp : 2 ≤ p) {i j : ℕ} (h : p * (p ^ 2) ^ i = p * (p ^ 2) ^ j) : i = j := by sorry
