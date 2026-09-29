-- Prove2me | Theorems.Thm_DiazModulus_conj_pair_quadratic_relation_iff
-- name    : DiazModulus.conj_pair_quadratic_relation_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T04:56:44.368186+00:00
-- url     : https://prove2.me/theorems/ead6580d-ba05-488b-aaf9-7ccf6fbb67b7
-- title:
--   The rational quadratic relations among u, ū, iπ are the identities Q(Im u, π) = s|u|²
-- statement:
--   **The homogeneous quadratic relations among $u$, $\bar u$, $i\pi$.**
--
--   Let $u = x + iy$ with $x \neq 0$ and $y \notin \mathbb{Q}\pi$, and let $a, b, c, d, e, f \in \mathbb{Q}$. Then
--
--   $$a u^{2} + b \bar u^{2} + c (i\pi)^{2} + d\, u\bar u + e\, u\, i\pi + f\, \bar u\, i\pi = 0$$
--
--   if and only if $a = b$, $e = -f$ and $(2a + d)(x^{2} + y^{2}) = 4a y^{2} + 2e\pi y + c\pi^{2}$.
--
--   So the rational homogeneous quadratic relations among $u$, $\bar u$ and $i\pi$ are exactly the identities $Q(\operatorname{Im} u, \pi) = s\,|u|^{2}$, with $Q$ a rational binary quadratic form and $s \in \mathbb{Q}$; here $Q = 4aY^{2} + 2eYP + cP^{2}$ and $s = 2a + d$. By `DiazModulus.generic_conj_pair_no_quadratic_relation` there are none when $u$ and $\pi$ are algebraically independent. No candidate for Diaz's conjecture carries such a relation. For $u$ algebraic over $\mathbb{Q}(\pi)$ with $e^{u}$ algebraic, $u$, $\bar u$, $i\pi$ are $\mathbb{Q}$-linearly independent logarithms of algebraic numbers in a field of transcendence degree one, and Théorème 0.2 of D. Roy and M. Waldschmidt (Ann. Sci. École Norm. Sup. 30, 1997) excludes every non-trivial rational quadratic relation among them. So the relations listed here, such as $\operatorname{Re}(u^{2}) = \pi^{2}$, occur only at points that are not candidates. (An earlier version of this text said that a candidate algebraic over $\mathbb{Q}(\pi)$ can carry them.)
--
--   **Novelty.** None claimed. Elementary: compare real and imaginary parts.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Proposition 5.7(a). Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Background: D. Roy and M. Waldschmidt, Ann. Sci. École Norm. Sup. (4) 30 (1997) 753–796.

import Mathlib

open ComplexConjugate

namespace DiazModulus

theorem conj_pair_quadratic_relation_iff (u : ℂ) (hre : u.re ≠ 0)
    (him : ∀ q : ℚ, u.im ≠ (q : ℝ) * Real.pi) (a b c d e f : ℚ) :
    (a : ℂ) * u ^ 2 + (b : ℂ) * conj u ^ 2 + (c : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2 + (d : ℂ) * (u * conj u)
        + (e : ℂ) * (u * (((Real.pi : ℝ) : ℂ) * Complex.I)) + (f : ℂ) * (conj u * (((Real.pi : ℝ) : ℂ) * Complex.I)) = 0 ↔
      a = b ∧ e = -f ∧
        (2 * (a : ℝ) + d) * (u.re ^ 2 + u.im ^ 2)
          = 4 * (a : ℝ) * u.im ^ 2 + 2 * (e : ℝ) * Real.pi * u.im + (c : ℝ) * Real.pi ^ 2 := by sorry

end DiazModulus
