-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_AA_of
-- name    : Formalism.InvariantFactorPaths.G7.coeff_AA_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:16.8948+00:00
-- url     : https://prove2.me/theorems/7c5146f6-a0d3-4685-b667-c17c8cd04937
-- title:
--   G7: coeff AA of
-- statement:
--   The G7 construction uses the coeff AA of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L189-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/TopsChoicePartA.lean#L189-L210

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

theorem Formalism.InvariantFactorPaths.G7.coeff_AA_of (K : Type) [Field K] {p : ℕ} (hp : 2 ≤ p) {x y : Fin 2} {n : Fin 2 →₀ ℕ}
    {i j : ℕ} (hij : i ≤ j) (hx : n x = (p ^ 2) ^ i) (hy : n y = p * (p ^ 2) ^ j) :
    MvPowerSeries.coeff n (AA K p x y) = ((p : K) ^ (i + j + 1))⁻¹ := by sorry
