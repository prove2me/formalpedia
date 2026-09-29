-- Prove2me | Theorems.Thm_DiazModulus_generic_qbar_homogeneous_four_exp_barrier
-- name    : DiazModulus.generic_qbar_homogeneous_four_exp_barrier
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T07:01:21.786001+00:00
-- url     : https://prove2.me/theorems/14af6f64-f229-43d8-9d05-cd1f10e295be
-- title:
--   For u algebraically independent of π on a circle of algebraic radius, no 2×2 configuration with Q̄-independent pairs lies over Q̄u + Q̄ū + Q̄iπ
-- statement:
--   **Algebraic coefficients do not help without a constant.**
--
--   Let $u \neq 0$ with $|u|^{2}$ algebraic, and suppose that $u$ and $i\pi$ are algebraically independent over $\overline{\mathbb{Q}}$. Then there are no $x_1, x_2$ and $y_1, y_2$, each pair linearly independent over $\overline{\mathbb{Q}}$, with all four products $x_i y_j$ in the $\overline{\mathbb{Q}}$-span of $u$, $\bar u$, $i\pi$.
--
--   So the homogeneous version of the strong four exponentials conjecture, with $\overline{\mathbb{Q}}$ in place of $\mathbb{Q}$ but no constant term, has no instance on the logarithms a generic candidate certifies. With rational coefficients this is `DiazModulus.generic_conj_pair_four_exp_barrier`. The configuration that does detect a candidate, $\begin{pmatrix}1 & \bar u\\ u & \rho\end{pmatrix}$, needs the constant, and `DiazModulus.generic_period_never_enters` shows that $i\pi$ cannot enter it. That homogeneity is what separates the provable from the open is classical; see the remark following Théorème 0.2 in Roy–Waldschmidt (1997), for quadrics in transcendence degree one.
--
--   **Novelty.** None claimed.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 5.4(c). Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi). Background: D. Roy and M. Waldschmidt, Ann. Sci. École Norm. Sup. (4) 30 (1997) 753–796.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem generic_qbar_homogeneous_four_exp_barrier (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    (x y : Fin 2 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y) :
    ¬ ∀ i j, x i * y j ∈ Submodule.span Qbar ({u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ) := by
  sorry

end DiazModulus
