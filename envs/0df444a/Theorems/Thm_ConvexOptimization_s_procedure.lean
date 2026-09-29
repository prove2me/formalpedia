-- Prove2me | Theorems.Thm_ConvexOptimization_s_procedure
-- name    : ConvexOptimization.s_procedure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:05:55.150864+00:00
-- url     : https://prove2.me/theorems/e2ccd87f-84f6-4253-9a60-61475957aa81
-- title:
--   The S-procedure (losslessness)
-- statement:
--   **The S-procedure** — the goal of this mission: one quadratic inequality implies another exactly when a single nonnegative multiplier certifies it.
--
--   Let $F_1, F_2$ be symmetric $n \times n$ real matrices, $g_1, g_2 \in \mathbb{R}^n$, $h_1, h_2 \in \mathbb{R}$, and set
--
--   $$q_k(x) \;=\; x^{T}F_k x + 2 g_k^{T} x + h_k \qquad (k = 1, 2),$$
--
--   with associated block matrices $M_k = \begin{bmatrix} F_k & g_k \\ g_k^{T} & h_k\end{bmatrix}$. Assume the strict-feasibility (Slater) condition: some $\hat{x}$ satisfies $q_1(\hat{x}) < 0$. Then
--
--   $$\bigl(q_1(x) \le 0 \Rightarrow q_2(x) \le 0 \ \text{ for every } x \in \mathbb{R}^n\bigr) \qquad\Longleftrightarrow\qquad \exists\, \lambda \ge 0 : \ \lambda M_1 - M_2 \;\succeq\; 0 .$$
--
--   The right-hand side is a linear matrix inequality in $\lambda$, so an implication between two quadratic inequalities — a statement quantified over all of $\mathbb{R}^n$, and in general nonconvex — becomes a small semidefinite feasibility problem. The direction $\Leftarrow$ is elementary; it is the converse, *losslessness*, that is the theorem, and it holds only for a pair of quadratics: with two or more constraints the analogous procedure is merely sufficient.
--
--   Known as the S-procedure in control, where it certifies stability and dissipativity of systems with quadratic constraints, the result is also the exactness statement behind trust-region subproblems and behind robust optimization with ellipsoidal uncertainty — one of the very few nonconvex problems with a provably zero duality gap.
--
--   **Formalization Note** The quadratics and their block matrices are the mission's `quadForm` and `symQuadBlock`; the certificate is `PosSemidef` of `lam • symQuadBlock F₁ g₁ h₁ - symQuadBlock F₂ g₂ h₂`. Strict feasibility is a hypothesis of the whole iff, matching the book. Source: B&V §B.2, p. 655, proved in §B.4, pp. 657–658.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 655, 657-658, §B.2 eq. (B.6)-(B.7) (the S-procedure for a single quadratic constraint), proof in §B.4

import Mathlib
import Definitions.Def_ConvexOptimization_quadraticForms

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.s_procedure {nn : ℕ}
    (F₁ F₂ : Matrix (Fin nn) (Fin nn) ℝ) (hF₁ : F₁.IsSymm) (hF₂ : F₂.IsSymm)
    (g₁ g₂ : Fin nn → ℝ) (h₁ h₂ : ℝ)
    (xh : Fin nn → ℝ) (hxh : quadForm F₁ g₁ h₁ xh < 0) :
    (∀ x, quadForm F₁ g₁ h₁ x ≤ 0 → quadForm F₂ g₂ h₂ x ≤ 0) ↔
      ∃ lam : ℝ, 0 ≤ lam ∧
        (lam • symQuadBlock F₁ g₁ h₁ - symQuadBlock F₂ g₂ h₂).PosSemidef := by
  sorry
