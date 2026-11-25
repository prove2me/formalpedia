-- Prove2me | Theorems.Thm_ConjCoord_gCount_prime
-- name    : ConjCoord.gCount_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:57:11.082831+00:00
-- url     : https://prove2.me/theorems/bd23188c-0fa7-534b-9a90-999067447620
-- title:
--   Conj Coord: g Count prime
-- statement:
--   The coefficient of `G θ(16)` at `p`: `gCount p ≡ 4 A (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L73-L76
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L73-L76

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_gCount_prime

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.gCount_prime {p : ℕ} (hp : p.Prime) (h5 : p % 16 = 5) {a b : ℤ}
    (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) :
    (gCount p : ℤ) ≡ 4 * octA b [ZMOD 8] := by sorry
