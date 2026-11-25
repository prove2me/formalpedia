-- Prove2me | Theorems.Thm_ConjCoord_octant_sum
-- name    : ConjCoord.octant_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:05:32.329931+00:00
-- url     : https://prove2.me/theorems/52823838-8713-4109-907e-0d15107b156e
-- title:
--   Conj Coord: octant sum
-- statement:
--   **Corollary 6 (the octant sum).** With Berndt's formula
--   `∑_{0<x<p/8} (x/p) = (h(-8p) - h(-4p))/4` for `p ≡ 5 (mod 8)` as a hypothesis,
--   `∑_{0<x<p/8} (x/p) ≡ 2 A (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L113-L118
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L113-L118

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_octant_sum

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.octant_sum (S : SturmInput phi 512) {p : ℕ} [Fact p.Prime] (h5 : p % 16 = 5)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h')
    (hBerndt : 4 * ∑ x ∈ Icc 1 (p / 8), legendreSym p x = (h' : ℤ) - h) :
    ∑ x ∈ Icc 1 (p / 8), legendreSym p x ≡ 2 * octA b [ZMOD 4] := by sorry
