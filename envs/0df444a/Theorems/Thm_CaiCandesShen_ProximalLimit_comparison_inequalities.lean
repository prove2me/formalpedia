-- Prove2me | Theorems.Thm_CaiCandesShen_ProximalLimit_comparison_inequalities
-- name    : CaiCandesShen.ProximalLimit.comparison_inequalities
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:24:47.5782+00:00
-- url     : https://prove2.me/theorems/c8cb4a84-46d4-414b-b7a5-cad38a56fd05
-- title:
--   Eq. (3.16) — the two comparison inequalities between $X^\star_\tau$ and $X_\infty$
-- statement:
--   Let $f_1,\dots,f_m:\mathbb R^{n_1\times n_2}\to\mathbb R$ be constraint functions, let $X_\infty$ be the minimum Frobenius norm solution (3.14) of the nuclear norm problem (1.6), and for $\tau>0$ let $X^\star_\tau$ be a solution of the proximal problem (3.4), which minimizes $f_\tau(X)=\tau\|X\|_*+\frac12\|X\|_F^2$ subject to $f_i(X)\le 0$, $i=1,\dots,m$. Then
--   $$\|X^\star_\tau\|_*+\frac{1}{2\tau}\|X^\star_\tau\|_F^2\le\|X_\infty\|_*+\frac{1}{2\tau}\|X_\infty\|_F^2\qquad\text{and}\qquad\|X_\infty\|_*\le\|X^\star_\tau\|_* .$$
--
--   The first inequality compares the two matrices in the proximal objective, divided by $\tau$; the second compares them in the nuclear norm. They are the first step of the proof of Theorem 3.1 and yield both the uniform Frobenius bound (3.17) and the convergence of the nuclear norms.
--
--   **Formalization Note** Only the defining minimality properties of $X^\star_\tau$ and $X_\infty$ are assumed; convexity and lower semicontinuity of the $f_i$, standing hypotheses of Theorem 3.1, are not needed for this step and are omitted, which makes the statement more general. The coefficient is written `1 / (2 * τ)` with $\tau>0$ assumed.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1967, proof of Theorem 3.1, Eq. (3.16)

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Eq. (3.16), p. 1967: for `τ > 0`, with `X⋆_τ` the solution of (3.4) and `X_∞` the minimum
Frobenius norm solution of (1.6),
`‖X⋆_τ‖_* + (1/(2τ))‖X⋆_τ‖_F² ≤ ‖X_∞‖_* + (1/(2τ))‖X_∞‖_F²` and `‖X_∞‖_* ≤ ‖X⋆_τ‖_*`. -/
theorem comparison_inequalities {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (τ : ℝ) (hτ : 0 < τ) (Xτ : Mat n₁ n₂) (hXτ : IsProximalSolution f τ Xτ) :
    nuclearNorm Xτ + 1 / (2 * τ) * frobNorm Xτ ^ 2 ≤
        nuclearNorm Xinf + 1 / (2 * τ) * frobNorm Xinf ^ 2 ∧
      nuclearNorm Xinf ≤ nuclearNorm Xτ := by sorry

end CaiCandesShen.ProximalLimit
