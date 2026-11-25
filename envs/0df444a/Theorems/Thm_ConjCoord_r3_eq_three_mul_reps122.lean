-- Prove2me | Theorems.Thm_ConjCoord_r3_eq_three_mul_reps122
-- name    : ConjCoord.r3_eq_three_mul_reps122
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:55:54.494297+00:00
-- url     : https://prove2.me/theorems/a9993473-9192-468a-9fa0-b596e854cb1f
-- title:
--   Conj Coord: r3 eq three mul reps122
-- statement:
--   Lemma 3, first part: `r₃(n) = 3 r_{1,2,2}(n)` for `n ≡ 1 (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L47-L48
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L47-L48

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_r3_eq_three_mul_reps122

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.r3_eq_three_mul_reps122 {n : ℕ} (hn : n % 4 = 1) : r3 n = 3 * reps 1 2 2 n := by sorry
