-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_det_mul_diagonal_mul_eq_sum
-- name    : Formalism.NuclearRankWeightBounds.P.det_mul_diagonal_mul_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:07.686081+00:00
-- url     : https://prove2.me/theorems/262a0b1d-9c51-4ca4-8115-19f8d745d155
-- title:
--   P: det mul diagonal mul eq sum
-- statement:
--   The P construction uses the det mul diagonal mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/DetMulDiagonalMulEqSum.lean#L7-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/DetMulDiagonalMulEqSum.lean#L7-L30

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DetMulDiagonalMulEqSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Polynomial Finset

theorem Formalism.NuclearRankWeightBounds.P.det_mul_diagonal_mul_eq_sum {R : Type*} [CommRing R] {n : Type*} [Fintype n]
    [DecidableEq n] {k : ℕ} (A : Matrix (Fin k) n R) (B : Matrix n (Fin k) R) (d : n → R) :
    (A * diagonal d * B).det =
      ∑ J ∈ powersetCard k (univ : Finset n),
        (∏ j ∈ J, d j) * ((B * A).submatrix (Subtype.val : J → n) Subtype.val).det := by sorry
