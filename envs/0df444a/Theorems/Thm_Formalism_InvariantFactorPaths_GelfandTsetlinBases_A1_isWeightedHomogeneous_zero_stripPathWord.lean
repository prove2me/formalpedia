-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_isWeightedHomogeneous_zero_stripPathWord
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.isWeightedHomogeneous_zero_stripPathWord
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:59.294817+00:00
-- url     : https://prove2.me/theorems/9dd742a0-7546-4e53-989a-9e60286a04b6
-- title:
--   A1: is Weighted Homogeneous zero strip Path Word
-- statement:
--   The A1 construction uses the is Weighted Homogeneous zero strip Path Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L236-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/IsWeightedHomogeneousZeroStripPathWord.lean#L236-L267

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
variable {R M : Type*} [CommRing R] [AddCommMonoid M] {n : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.isWeightedHomogeneous_zero_stripPathWord (w : ℕ × Fin n → M) (N : ℕ) (hw : ∀ x : ℕ × Fin n, x.1 ≠ N → w x = 0)
    (isVec : ℕ → Bool) (μ : ℕ → Fin n → ℤ) (c : ℤ) : ∀ j ≤ N, ∀ J,
    IsWeightedHomogeneous w (pathWord isVec μ c (XR R n) j J) 0 := by sorry
