-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_coordinate_equiv
-- name    : D1Bound5.IsD1Tuple.coordinate_equiv
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:46.422612+00:00
-- url     : https://prove2.me/theorems/e9a80695-a584-48a5-bfb5-9d34bdcc45f4
-- title:
--   Ring isomorphisms preserve Diophantine tuples
-- statement:
--   Let $R$ and $S$ be commutative rings, let $n$ be a nonnegative integer, and let $e:R\to S$ be a ring isomorphism. If $t:\{0,\ldots,n-1\}\to R$ is an injective Diophantine tuple of nonzero elements, then
--   $$i\longmapsto e(t(i))$$
--   is a Diophantine tuple in $S$. The assertion includes all pairwise square witnesses.
-- source:
--   D1Bound5/DegeneratePairImpossible.lean, D1Bound5.IsD1Tuple.coordinate_equiv, lines 27-37; original file SHA-256 449a3a0eb81ab63cbb073585d13a396c6886de6c7e8f6b4565307a657ed38f67. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Ring.Equiv
import Definitions.Def_D1Bound5_IsD1Tuple

open D1Bound5

theorem D1Bound5.IsD1Tuple.coordinate_equiv {R S : Type*} [CommRing R] [CommRing S]
    {n : ℕ} (t : Fin n → R) (ht : IsD1Tuple t) (e : R ≃+* S) :
    IsD1Tuple (fun i => e (t i)) := by sorry
