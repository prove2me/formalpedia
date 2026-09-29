-- Prove2me | Theorems.Thm_DiazModulus_anisotropic_relation_four_exp_barrier
-- name    : DiazModulus.anisotropic_relation_four_exp_barrier
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T05:04:44.391828+00:00
-- url     : https://prove2.me/theorems/2f059369-975e-4205-86a3-3981e971ea86
-- title:
--   An anisotropic quadratic relation among u, ū, iπ yields no four exponentials configuration
-- statement:
--   **Anisotropic relations are invisible to four exponentials.**
--
--   Let $u = x + iy$ with $x \neq 0$, $y \notin \mathbb{Q}\pi$ and $|u|^{2}$ algebraic. Suppose that $u$, $\bar u$, $i\pi$ satisfy a rational quadratic relation $F(u, \bar u, i\pi) = 0$ whose form $F$ has no non-trivial rational zero. Then every singular $2\times2$ matrix whose entries are rational linear combinations of $u$, $\bar u$, $i\pi$ has $\mathbb{Q}$-linearly dependent rows or $\mathbb{Q}$-linearly dependent columns.
--
--   Such relations occur: `DiazModulus.anisotropic_relation_on_circle` gives points with $\operatorname{Re}(u^{2}) = \pi^{2}$ on every circle of algebraic radius greater than $\pi$. The statement uses only the transcendence of $\pi$ and holds for every such $u$, candidate or not: up to a rational factor $F$ is the only relation $u$ carries, and it is not the determinant of a $2\times2$ matrix of rational linear forms (`DiazModulus.det_linear_forms_isotropic`), so no $2\times2$ configuration sees it. Larger configurations do. By Théorème 0.2 of D. Roy and M. Waldschmidt (Ann. Sci. École Norm. Sup. 30, 1997), $\mathbb{Q}$-linearly independent logarithms of algebraic numbers in a field of transcendence degree one satisfy no non-trivial rational quadratic relation; their proof goes through larger matrices, via the Clifford algebra of the form. Such $u$ is algebraic over $\mathbb{Q}(\pi)$, so no point carrying an anisotropic relation is a candidate. (An earlier version of this text said that no proved theorem was known to exclude such a candidate; that was wrong.)
--
--   **Novelty.** None claimed.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Proposition 5.7(b). Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Background: D. Roy and M. Waldschmidt, Ann. Sci. École Norm. Sup. (4) 30 (1997) 753–796.

import Mathlib

open ComplexConjugate

namespace DiazModulus

theorem anisotropic_relation_four_exp_barrier (u : ℂ) (hre : u.re ≠ 0)
    (him : ∀ q : ℚ, u.im ≠ (q : ℝ) * Real.pi) (hρ : IsAlgebraic ℚ (u * conj u))
    (a b c d e f : ℚ)
    (hrel : (a : ℂ) * u ^ 2 + (b : ℂ) * conj u ^ 2 + (c : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2
        + (d : ℂ) * (u * conj u) + (e : ℂ) * (u * (((Real.pi : ℝ) : ℂ) * Complex.I))
        + (f : ℂ) * (conj u * (((Real.pi : ℝ) : ℂ) * Complex.I)) = 0)
    (hanis : ∀ v : Fin 3 → ℚ, a * v 0 ^ 2 + b * v 1 ^ 2 + c * v 2 ^ 2 + d * (v 0 * v 1)
        + e * (v 0 * v 2) + f * (v 1 * v 2) = 0 → v = 0)
    (A : Fin 2 → Fin 2 → Fin 3 → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = ∑ k, (A i j k : ℂ) * ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by sorry

end DiazModulus
