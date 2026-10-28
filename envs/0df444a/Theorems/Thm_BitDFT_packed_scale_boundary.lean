-- Prove2me | Theorems.Thm_BitDFT_packed_scale_boundary
-- name    : BitDFT.packed_scale_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T02:24:39.095867+00:00
-- url     : https://prove2.me/theorems/640ab1ca-b876-49e6-9e1c-c6ee332aac0e
-- title:
--   Keep the maximal fixed-point coordinate inside the packed digit
-- statement:
--   Let a packed block contain signed coordinates with magnitudes at most 2^q, including the boundary value. Suppose the scale factor n is at most 2^ell, ell is at most q, and q is at least 2. After multiplying every coordinate by n, each result has magnitude strictly below half the balanced base 2^(3q). Balanced unpacking therefore recovers the scaled coordinates without a carry crossing a digit boundary, including at the exact input magnitude limit.
-- source:
--   Boundary-strengthening lemma needed to apply balanced Kronecker packing to the full disc bound in BitDFT.rescale_output_machine.

import Definitions.Def_BitDFT_PackedScale
import Mathlib.Tactic
set_option autoImplicit false
open IntMul BitDFT.PackedScale

theorem BitDFT.packed_scale_boundary (n q ell : ℕ) (hn : n ≤ 2^ell)
    (hell : ell ≤ q) (hq : 2 ≤ q)
    (xs : List ℤ) (hxs : ∀ x ∈ xs, x.natAbs ≤ 2^q) :
    ∀ x ∈ xs, ((n : ℤ) * x).natAbs < 2^(3*q-1) := by sorry
