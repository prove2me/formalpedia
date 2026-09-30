-- Prove2me | Theorems.Thm_CaiCandesShen_ProximalLimit_proximal_solution_tendsto_min_norm
-- name    : CaiCandesShen.ProximalLimit.proximal_solution_tendsto_min_norm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:27:28.183218+00:00
-- url     : https://prove2.me/theorems/e2486b5f-f111-4ec9-9060-76e65eb68e26
-- title:
--   Theorem 3.1 — $\lim_{\tau\to\infty}\|X^\star_\tau - X_\infty\|_F = 0$
-- statement:
--   Let $f_1,\dots,f_m:\mathbb R^{n_1\times n_2}\to\mathbb R$ be convex and lower semicontinuous, and consider the nuclear norm problem
--   $$\text{(1.6)}\qquad\text{minimize } \|X\|_*\quad\text{subject to } f_i(X)\le 0,\ i=1,\dots,m,$$
--   and, for $\tau>0$, the proximal problem
--   $$\text{(3.4)}\qquad\text{minimize } f_\tau(X)=\tau\|X\|_*+\tfrac12\|X\|_F^2\quad\text{subject to } f_i(X)\le 0,\ i=1,\dots,m.$$
--   Let $X_\infty$ be the minimum Frobenius norm solution to (1.6),
--   $$X_\infty:=\arg\min_X\{\|X\|_F^2 : X\text{ is a solution of (1.6)}\},$$
--   and for each $\tau>0$ let $X^\star_\tau$ be the solution to (3.4). Then
--   $$\lim_{\tau\to\infty}\|X^\star_\tau-X_\infty\|_F=0 .$$
--
--   Minimizing the proximal objective $f_\tau$, which is what the singular value thresholding iteration does, is therefore the same as minimizing the nuclear norm in the limit of large $\tau$, and the limit selects the solution of (1.6) of least Frobenius norm.
--
--   **Formalization Note** $X^\star_\tau$ is a family `Xτ : ℝ → Mat n₁ n₂` assumed to solve (3.4) for every $\tau>0$; its values at $\tau\le 0$ are unconstrained and irrelevant to the limit along `Filter.atTop` on $\mathbb R$. $X_\infty$ is assumed to have the defining property (3.14); this presupposes, as the paper's definition does, that (1.6) has a solution, and the hypotheses can be met exactly when the feasible set is nonempty (the statement is vacuous otherwise, where $X_\infty$ is undefined in the paper too). Uniqueness of $X_\infty$ is not assumed. Convexity is `ConvexOn ℝ Set.univ`, lower semicontinuity is `LowerSemicontinuous`; $m=0$ is allowed.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1967, Theorem 3.1, Eqs. (3.14), (3.15)

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic
import Definitions.Def_CaiCandesShen_ProximalLimit_Problems
open Filter Topology

namespace CaiCandesShen.ProximalLimit

/-- Theorem 3.1, p. 1967: let `X⋆_τ` be the solution to (3.4) and `X_∞` the minimum Frobenius norm
solution (3.14) to (1.6). If the `f_i` are convex and lower semicontinuous, then
`lim_{τ→∞} ‖X⋆_τ - X_∞‖_F = 0` (eq. (3.15)). -/
theorem proximal_solution_tendsto_min_norm {m n₁ n₂ : ℕ} (f : Fin m → Mat n₁ n₂ → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hlsc : ∀ i, LowerSemicontinuous (f i))
    (Xinf : Mat n₁ n₂) (hXinf : IsMinFrobeniusSolution f Xinf)
    (Xτ : ℝ → Mat n₁ n₂) (hXτ : ∀ τ, 0 < τ → IsProximalSolution f τ (Xτ τ)) :
    Tendsto (fun τ => frobNorm (Xτ τ - Xinf)) atTop (𝓝 0) := by sorry

end CaiCandesShen.ProximalLimit
