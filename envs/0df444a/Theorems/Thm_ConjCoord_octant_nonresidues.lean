-- Prove2me | Theorems.Thm_ConjCoord_octant_nonresidues
-- name    : ConjCoord.octant_nonresidues
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:05:54.151738+00:00
-- url     : https://prove2.me/theorems/db40482c-172e-5f15-bb01-b1292cb0cd5c
-- title:
--   Conj Coord: octant nonresidues
-- statement:
--   **Corollary 6, second form**: the number of quadratic nonresidues in `(0, p/8)` is
--   `≡ (p - 5)/16 + A (mod 2)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L122-L128
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L122-L128

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_octant_nonresidues

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.octant_nonresidues (S : SturmInput phi 512) {p : ℕ} [Fact p.Prime]
    (h5 : p % 16 = 5) {a b : ℤ} (hab : a ^ 2 + b ^ 2 = p) (hb : Even b) {h h' : ℕ}
    (hG : r3 p = 12 * h) (hG' : r3 (2 * p) = 12 * h')
    (hBerndt : 4 * ∑ x ∈ Icc 1 (p / 8), legendreSym p x = (h' : ℤ) - h) :
    (((Icc 1 (p / 8)).filter fun x : ℕ => legendreSym p (x : ℤ) = -1).card : ℤ) ≡
      ((p - 5) / 16 : ℕ) + octA b [ZMOD 2] := by sorry
