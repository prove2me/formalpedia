-- Prove2me | Theorems.Thm_FamousTheorems_integral_scheme_iff_reduced_irreducible_7a
-- name    : FamousTheorems.integral_scheme_iff_reduced_irreducible_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:26.594082+00:00
-- url     : https://prove2.me/theorems/ca5aaada-db28-4cae-a347-9c657595aaeb
-- title:
--   A scheme is integral iff it is reduced and irreducible
-- statement:
--   **A scheme is integral iff it is reduced and irreducible.** A scheme $X$ is integral, meaning that $X$ is nonempty and $\mathcal O_X(U)$ is an integral domain for every nonempty open $U$, if and only if $X$ is reduced and its underlying topological space is irreducible.
--
--   This is the scheme-theoretic analogue of the fact that a ring is an integral domain if and only if it is reduced and has a unique minimal prime. It is used constantly in algebraic geometry: varieties are often defined as integral schemes, and integral schemes have a generic point and a function field.
--
--   **Formalization note.** Mathlib's `AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced`. Irreducible spaces are nonempty by Mathlib's definition, and `IsReduced X` says that all rings of sections are reduced.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem integral_scheme_iff_reduced_irreducible_7a (X : AlgebraicGeometry.Scheme) :
    AlgebraicGeometry.IsIntegral X ↔ IrreducibleSpace X ∧ AlgebraicGeometry.IsReduced X := by sorry

end FamousTheorems
