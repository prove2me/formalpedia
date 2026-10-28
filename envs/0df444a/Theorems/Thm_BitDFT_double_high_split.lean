-- Prove2me | Theorems.Thm_BitDFT_double_high_split
-- name    : BitDFT.double_high_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T01:45:40.514322+00:00
-- url     : https://prove2.me/theorems/e2400c2d-1236-48fb-a4bf-cbb8a8469464
-- title:
--   Two boundary-width magnitudes reduce to one q-bit product
-- statement:
--   Let q be a positive precision and let a,b≤2^q be nonnegative integer magnitudes. If either magnitude has its q-th bit set, that magnitude is exactly 2^q and its product is obtained by a shift. Otherwise the product is the product of the two residues modulo 2^q. Thus the only nontrivial multiplication needed is between two q-bit residues, even when both inputs lie on the boundary.
-- source:
--   Width-p reduction used in the fixed-point complex-multiplication machine for the integer-multiplication-to-DFT transfer.

import Theorems.Thm_BitDFT_scalar_low_product_selection
import Mathlib.Tactic
open IntMul

theorem BitDFT.double_high_split (q a b : ℕ) (ha : a ≤ 2^q) (hb : b ≤ 2^q) :
    a * b = if a.testBit q then 2^q * b
      else if b.testBit q then (a % 2^q) * 2^q
      else (a % 2^q) * (b % 2^q) := by sorry
