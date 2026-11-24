-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_frobVar_AA_ne_zero
-- name    : Formalism.InvariantFactorPaths.G7.coeff_frobVar_AA_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:23.80938+00:00
-- url     : https://prove2.me/theorems/e875a5bd-b79d-4330-9322-93bc395bdaf6
-- title:
--   G7: coeff frob Var AA ne zero
-- statement:
--   The G7 construction uses the coeff frob Var AA ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L243-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L243-L248

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

theorem Formalism.InvariantFactorPaths.G7.coeff_frobVar_AA_ne_zero {K : Type} [Field K] {p : ℕ} (hp : 2 ≤ p) {x y : Fin 2}
    {n : Fin 2 →₀ ℕ} (h : MvPowerSeries.coeff n (frobVar p (AA K p x y)) ≠ 0) :
    ∃ i j, i ≤ j ∧ n x = p * (p ^ 2) ^ i ∧ n y = (p ^ 2) ^ (j + 1) := by sorry
