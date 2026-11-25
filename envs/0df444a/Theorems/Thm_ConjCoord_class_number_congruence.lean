-- Prove2me | Theorems.Thm_ConjCoord_class_number_congruence
-- name    : ConjCoord.class_number_congruence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:03:27.83249+00:00
-- url     : https://prove2.me/theorems/7855a1d9-5552-47bb-9242-b4dd040f93ba
-- title:
--   Conj Coord: class number congruence
-- statement:
--   **Theorem 1.** For a prime `p ≡ 5 (mod 16)`, `p = a² + b²` with `b` even, and `h = h(-4p)`,
--   `h' = h(-8p)` given through Gauss's `r₃(p) = 12 h(-4p)` and `r₃(2p) = 12 h(-8p)`:
--   `h(-8p) ≡ h(-4p) + 8 A (mod 16)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L93-L97
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L93-L97

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_class_number_congruence

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.class_number_congruence (S : SturmInput phi 512) {p : ℕ} (hp : p.Prime)
    (h5 : p % 16 = 5) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h') :
    (h' : ℤ) ≡ h + 8 * octA b [ZMOD 16] := by sorry
