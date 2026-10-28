-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_simultaneous_neg
-- name    : D1Bound5.IsD1Tuple.simultaneous_neg
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:49.457366+00:00
-- url     : https://prove2.me/theorems/61da1b9c-6d24-41b7-afd1-c5b60aed433b
-- title:
--   Simultaneous negation preserves Diophantine tuples
-- statement:
--   Let $R$ be a commutative ring and let $t:\{0,\ldots,n-1\}\to R$ be a Diophantine tuple. Then
--   $$i\longmapsto -t(i)$$
--   is also a Diophantine tuple. All entries remain distinct and nonzero, and the same square witnesses work for every pair.
-- source:
--   D1Bound5/DegeneratePairImpossible.lean, D1Bound5.IsD1Tuple.simultaneous_neg, lines 12-25; original file SHA-256 449a3a0eb81ab63cbb073585d13a396c6886de6c7e8f6b4565307a657ed38f67. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Ring.Equiv
import Definitions.Def_D1Bound5_IsD1Tuple

open D1Bound5

theorem D1Bound5.IsD1Tuple.simultaneous_neg {R : Type*} [CommRing R] {n : ℕ}
    (t : Fin n → R) (ht : IsD1Tuple t) : IsD1Tuple (fun i => -t i) := by sorry
