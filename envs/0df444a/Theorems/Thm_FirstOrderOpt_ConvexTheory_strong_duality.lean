-- Prove2me | Theorems.Thm_FirstOrderOpt_ConvexTheory_strong_duality
-- name    : FirstOrderOpt.ConvexTheory.strong_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T20:54:24.944851+00:00
-- url     : https://prove2.me/theorems/124bd975-70dd-4af1-bfd7-37f07b7879c0
-- title:
--   Theorem 2.6 — strong duality under Slater's condition
-- statement:
--   Consider the convex program (2.3.16) with $X \subseteq \mathbb{R}^n$ closed convex, $f,
--   g_1,\dots,g_m$ convex on $X$, and $h_1,\dots,h_p$ affine. Write $f^*$ for the primal optimal
--   value (the greatest lower bound of $f$ over the feasible set) and
--   $$\varphi^* := \max_{\lambda \ge 0,\, y} \varphi(\lambda, y), \qquad \varphi(\lambda,y) :=
--   \min_{x \in X} L(x,\lambda,y)$$
--   for the Lagrange dual value, $L$ the Lagrangian above.
--
--   **Theorem 2.6.** Suppose (2.3.16) is bounded below and there exists $\bar x \in
--   \operatorname{int} X$ with $g(\bar x) < 0$ and $h(\bar x) = 0$ (Slater's condition). Then the
--   Lagrange dual is solvable and $\varphi^* = f^*$.
--
--   Weak duality ($\varphi^* \le f^*$) always holds by construction; strong duality is the much
--   harder equality, and Lan proves it from the separation theorem via the Convex Theorem on
--   Alternative (Proposition 2.9).
--
--   **Formalization Note.** $h_j$ affine is represented concretely by witnesses $w_j \in
--   \mathbb{R}^n, b_j \in \mathbb{R}$ with $h_j(x) = \langle w_j, x\rangle + b_j$, rather than an
--   abstract affine-map predicate, since $\nabla h_j = w_j$ is exactly what Theorem 2.8's
--   stationarity condition needs later. "$f^*$" is the real number witnessing $\mathrm{IsGLB}(f
--   \,''\, \mathrm{Feasible},\, f^*)$ rather than a raw `sInf`, so the hypothesis carries no
--   hidden claim about the feasible set's boundedness or nonemptiness (both follow here from the
--   Slater point). The conclusion packages "dual solvable and $\varphi^*=f^*$" as: some
--   $(\lambda^*, y^*)$ with $\lambda^* \ge 0$ attains $\inf_{x\in X} L(x,\lambda^*,y^*) = f^*$; by
--   weak duality this $(\lambda^*,y^*)$ is automatically the maximizer, so this is equivalent to
--   Lan's two-clause conclusion.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 39, Theorem 2.6

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_lagrangian

namespace FirstOrderOpt.ConvexTheory

/-- Theorem 2.6 (strong duality under Slater's condition). For the convex program (2.3.16)
with `X` closed convex, `f, g` convex, `h` affine (given via witnesses `w, b`), a Slater point
`x̄ ∈ int X` with `g(x̄) < 0`, `h(x̄) = 0`, and primal optimal value `fStar` (the greatest lower
bound of `f` over the feasible set): the Lagrange dual is solvable and attains `fStar`, i.e.
there are multipliers `λ* ≥ 0, y*` at which `inf_{x ∈ X} L(x, λ*, y*) = fStar`. -/
theorem strong_duality {n m p : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (h : Fin p → EuclideanSpace ℝ (Fin n) → ℝ)
    (hh : ∀ j x, h j x = inner ℝ (w j) x + b j)
    (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (hfconv : ConvexOn ℝ X f) (hgconv : ∀ i, ConvexOn ℝ X (g i))
    (Feasible : Set (EuclideanSpace ℝ (Fin n)))
    (hFeasible : Feasible = {x ∈ X | (∀ i, g i x ≤ 0) ∧ (∀ j, h j x = 0)})
    (fStar : ℝ) (hfStar : IsGLB (f '' Feasible) fStar)
    (barx : EuclideanSpace ℝ (Fin n)) (hbarx_int : barx ∈ interior X)
    (hbarx_g : ∀ i, g i barx < 0) (hbarx_h : ∀ j, h j barx = 0) :
    ∃ lamStar : Fin m → ℝ, ∃ yStar : Fin p → ℝ, (∀ i, 0 ≤ lamStar i) ∧
      IsGLB ((fun x => lagrangian f g h x lamStar yStar) '' X) fStar := by sorry

end FirstOrderOpt.ConvexTheory
