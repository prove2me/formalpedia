-- Prove2me | Theorems.Thm_ConjCoord_Proof_reps_congruence
-- name    : ConjCoord.Proof.reps_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:51:29.67911+00:00
-- url     : https://prove2.me/theorems/80bd41eb-7a42-5665-9485-7b2b6658c3c3
-- title:
--   Proof: reps congruence
-- statement:
--   **The congruence for representation numbers**: for a prime `p ≡ 5 (mod 16)` with
--   `p = a² + b²`, `b` even, `2 r_{1,2,4}(p) - r_{1,2,2}(p) ≡ 32 A (mod 64)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L106-L114
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L106-L114

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.reps_congruence (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    2 * (reps 1 2 4 p : ℤ) - reps 1 2 2 p ≡ 32 * octA b [ZMOD 64] := by sorry
