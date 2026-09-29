-- Prove2me | Theorems.Thm_FamousTheorems_isaacs_alg_closure_criterion_6b
-- name    : FamousTheorems.isaacs_alg_closure_criterion_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:24.157546+00:00
-- url     : https://prove2.me/theorems/60ba960e-7212-4ef4-8d26-55d23ccdfe91
-- title:
--   Isaacs's theorem: an algebraic extension in which every polynomial has a root is an algebraic closure
-- statement:
--   **Isaacs's theorem on algebraic closures.** Let $E/F$ be an algebraic field extension such that every nonconstant polynomial in $F[x]$ has a root in $E$. Then $E$ is algebraically closed, and hence an algebraic closure of $F$.
--
--   The hypothesis concerns only polynomials with coefficients in $F$, yet the conclusion covers all polynomials over $E$. For perfect fields the result follows from the primitive element theorem. Isaacs proved it in general in 1980 by a counting argument over finite-dimensional subextensions.
--
--   **Formalization note.** Mathlib's `IsAlgClosure.of_exists_root`. It suffices to assume that every monic irreducible polynomial over $F$ has a root in $E$. `IsAlgClosure F E` says that $E$ is algebraically closed and algebraic over $F$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsAlgClosure.of_exists_root`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem isaacs_alg_closure_criterion_6b {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]
    (h : ∀ p : Polynomial F, p.Monic → Irreducible p → ∃ x : E, Polynomial.aeval x p = 0) : IsAlgClosure F E := by sorry

end FamousTheorems
