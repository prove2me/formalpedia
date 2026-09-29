-- Prove2me | Theorems.Thm_DiazModulus_generic_quadratic_relation_is_norm
-- name    : DiazModulus.generic_quadratic_relation_is_norm
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T04:56:53.447902+00:00
-- url     : https://prove2.me/theorems/835b0305-9121-4c4b-a5d6-9aa2cc5f7bb1
-- title:
--   For u algebraically independent of π on a circle of algebraic radius, every algebraic quadratic relation among 1, u, ū, iπ is a multiple of the norm
-- statement:
--   **With a constant term, the norm is the only quadratic relation.**
--
--   Let $u \neq 0$ with $\rho = |u|^{2}$ algebraic, and suppose that $u$ and $i\pi$ are algebraically independent over $\overline{\mathbb{Q}}$. If a quadratic form $P$ in four variables with algebraic coefficients vanishes at $(1, u, \bar u, i\pi)$, then
--
--   $$P = c\,(X_1X_2 - \rho X_0^{2})$$
--
--   as a function on $\mathbb{C}^{4}$, for some algebraic $c$.
--
--   This extends `DiazModulus.generic_conj_pair_no_quadratic_relation` to algebraic coefficients and to relations with a constant term. In particular, a relation without constant term is trivial: the relation $u\bar u = \rho$ needs the constant.
--
--   **Novelty.** None claimed.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 5.6(a). Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem generic_quadratic_relation_is_norm (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (P : Fin 4 → Fin 4 → ℂ) (hP : ∀ k l, IsAlgebraic ℚ (P k l))
    (hrel : ∑ k, ∑ l, P k l * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k
      * ![1, u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] l = 0) :
    ∃ c : ℂ, IsAlgebraic ℚ c ∧
      ∀ x : Fin 4 → ℂ, ∑ k, ∑ l, P k l * x k * x l = c * (x 1 * x 2 - u * conj u * x 0 ^ 2) := by
  sorry

end DiazModulus
