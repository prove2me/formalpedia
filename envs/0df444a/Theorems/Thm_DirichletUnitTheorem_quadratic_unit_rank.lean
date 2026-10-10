-- Prove2me | Theorems.Thm_DirichletUnitTheorem_quadratic_unit_rank
-- name    : DirichletUnitTheorem.quadratic_unit_rank
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:48.334984+00:00
-- url     : https://prove2.me/theorems/39fde9cf-d34f-48f2-8838-7652e9d09a8f
-- title:
--   Unit rank of quadratic fields
-- statement:
--   Let $K$ be a quadratic number field, $[K:\mathbb Q]=2$. Then
--
--   1. the unit rank of $K$ is $1$ if and only if $K$ is a real quadratic field (both embeddings are real), and
--   2. the unit rank of $K$ is $0$ if and only if $K$ is an imaginary quadratic field (no embedding is real).
--
--   For real quadratic fields this is the theory of Pell's equation.
--
--   **Formalization Note** "Real quadratic" is encoded as Mathlib's `IsTotallyReal` and "imaginary quadratic" as `IsTotallyComplex`; for degree $2$ these agree with the usual notions.
-- source:
--   Wikipedia, "Dirichlet's unit theorem" (article supplied by the account owner as a PDF), lead section ("if K is a quadratic field, the rank is 1 if it is a real quadratic field, and 0 if an imaginary quadratic field").

import Mathlib
open NumberField

namespace DirichletUnitTheorem

theorem quadratic_unit_rank (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) :
    (Module.rank ℤ (Additive (𝓞 K)ˣ) = 1 ↔ IsTotallyReal K) ∧
      (Module.rank ℤ (Additive (𝓞 K)ˣ) = 0 ↔ IsTotallyComplex K) := by sorry

end DirichletUnitTheorem
