-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_vecMul_inv_eq_iff
-- name    : Formalism.LogVandermondeBounds.StandardLattice.vecMul_inv_eq_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:14.72499+00:00
-- url     : https://prove2.me/theorems/1ba3c55c-2f99-4380-b3e3-6c66e78be847
-- title:
--   Standard Lattice: vec Mul inv eq iff
-- statement:
--   The Standard Lattice construction uses the vec Mul inv eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/CardStabilizerVector.lean#L103-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/CardStabilizerVector.lean#L103-L116

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset

theorem Formalism.LogVandermondeBounds.StandardLattice.vecMul_inv_eq_iff {F : Type} [Field F] {n : ℕ} (v : Fin n → F) (A : GL (Fin n) F) :
    Matrix.vecMul v ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = v ↔
      Matrix.vecMul v (A : Matrix (Fin n) (Fin n) F) = v := by sorry
