-- Prove2me | Theorems.Thm_ConjCoord_reps_congruence
-- name    : ConjCoord.reps_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:02:05.536376+00:00
-- url     : https://prove2.me/theorems/5e1b739c-d136-4d51-99d9-6bc27e885085
-- title:
--   Conj Coord: reps congruence
-- statement:
--   The congruence for representation numbers: `2 r_{1,2,4}(p) - r_{1,2,2}(p) ≡ 32 A (mod 64)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L79-L82
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L79-L82

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_reps_congruence

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.reps_congruence (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    2 * (reps 1 2 4 p : ℤ) - reps 1 2 2 p ≡ 32 * octA b [ZMOD 64] := by sorry
