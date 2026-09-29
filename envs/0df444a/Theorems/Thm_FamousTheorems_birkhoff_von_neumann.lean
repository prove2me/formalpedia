-- Prove2me | Theorems.Thm_FamousTheorems_birkhoff_von_neumann
-- name    : FamousTheorems.birkhoff_von_neumann
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:21.31024+00:00
-- url     : https://prove2.me/theorems/bf8831c5-ab4a-48f4-bd33-b03cacac4f44
-- title:
--   The Birkhoff–von Neumann theorem
-- statement:
--   **The Birkhoff–von Neumann theorem.** Over an ordered field, the set of $n\times n$ doubly stochastic matrices (nonnegative entries, all row and column sums $1$) is the convex hull of the permutation matrices.
--
--   Equivalently, the permutation matrices are the extreme points of the Birkhoff polytope. The theorem is the basis of the assignment problem in linear programming and of majorisation theory, and it is equivalent to Hall's and König's theorems on bipartite matchings.
--
--   **Formalization note.** Mathlib's `doublyStochastic_eq_convexHull_permMatrix`; `doublyStochastic R n` is a submonoid of matrices and `Equiv.Perm.permMatrix R σ` is the permutation matrix of `σ`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `doublyStochastic_eq_convexHull_permMatrix`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem birkhoff_von_neumann {R n : Type*} [Fintype n] [DecidableEq n] [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    (doublyStochastic R n : Set (Matrix n n R)) =
      convexHull R {x : Matrix n n R | ∃ σ : Equiv.Perm n, Equiv.Perm.permMatrix R σ = x} := by sorry

end FamousTheorems
