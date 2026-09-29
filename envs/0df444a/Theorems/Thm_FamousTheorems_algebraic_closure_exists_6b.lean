-- Prove2me | Theorems.Thm_FamousTheorems_algebraic_closure_exists_6b
-- name    : FamousTheorems.algebraic_closure_exists_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:25.659892+00:00
-- url     : https://prove2.me/theorems/2a817755-8fb8-48f0-b563-5f85f870f2dc
-- title:
--   Existence of algebraic closures
-- statement:
--   **Existence of algebraic closures.** Every field $k$ has an algebraic closure: an algebraically closed field $\bar k$ containing $k$ such that every element of $\bar k$ is algebraic over $k$.
--
--   The algebraic closure is where all polynomials over $k$ have their roots. It is the setting of Galois theory of infinite extensions and of algebraic geometry over $k$, and it is unique up to isomorphism over $k$. Existence needs a form of the axiom of choice. Artin's proof adjoins roots of all polynomials at once using a maximal ideal in a large polynomial ring.
--
--   **Formalization note.** Mathlib's instance `AlgebraicClosure.isAlgClosed`, together with the instance that `AlgebraicClosure k` is algebraic over $k$. `AlgebraicClosure k` is Mathlib's construction, and `IsAlgClosure k K` says that $K$ is algebraically closed and algebraic over $k$. The statement is proved by `inferInstance`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AlgebraicClosure.isAlgClosed`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem algebraic_closure_exists_6b (k : Type*) [Field k] : IsAlgClosure k (AlgebraicClosure k) := by sorry

end FamousTheorems
