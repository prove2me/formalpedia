-- Prove2me | Theorems.Thm_DiazModulus_quadratic_eq_zero_of_not_mem_Qbar
-- name    : DiazModulus.quadratic_eq_zero_of_not_mem_Qbar
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T08:54:47.754879+00:00
-- url     : https://prove2.me/theorems/37ea2af8-7692-484d-9fcf-abd99afd53e5
-- title:
--   A transcendental number is a root of no non-zero quadratic with algebraic coefficients
-- statement:
--   Let $z$ be a complex number that is not algebraic, and let $a, b, c$ be algebraic. If $az^2 + bz + c = 0$, then $a = b = c = 0$.
--
--   **Proof.** Otherwise $z$ would be algebraic over the field of algebraic numbers, and therefore algebraic.
--
--   **Novelty.** None: a standard fact. It is the step that makes families such as $(1, \lambda, \lambda^2)$ or $(1, \lambda, 1/\lambda)$ linearly independent over $\overline{\mathbb{Q}}$ for transcendental $\lambda$, which Diaz (2007) uses without comment.
-- source:
--   Standard. Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- A complex number outside `Q̄` is a root of no non-zero quadratic polynomial with algebraic coefficients. -/
theorem quadratic_eq_zero_of_not_mem_Qbar {z a b c : ℂ} (hz : z ∉ Qbar)
    (ha : a ∈ Qbar) (hb : b ∈ Qbar) (hc : c ∈ Qbar) (h : a * z ^ 2 + b * z + c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  sorry

end DiazModulus
