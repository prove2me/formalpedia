-- Prove2me | Theorems.Thm_BarrierTR_Global_lemma_4_5
-- name    : BarrierTR.Global.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:02.166997+00:00
-- url     : https://prove2.me/theorems/25997f25-fb4f-4fb6-9377-a684e486f55d
-- title:
--   Lemma 4.5, p. 24 — the iterates approach stationarity of ‖g(x)+s‖²: (A_k; S_k)(g_k + s_k) → 0
-- statement:
--   Consider a run of Algorithm I applied to (2.2). Assume that the sequences $\{g_k\}$, $\{A_k\}$ and $\{B_k\}$ are bounded, that $\{f_k\}$ is bounded below, and that $g$, $A$ and $\nabla f$ are Lipschitz continuous on an open set containing all the iterates $x_k$. Then
--   $$\lim_{k\to\infty}\binom{A_k}{S_k}(g_k+s_k)=0,$$
--   that is, $A_k(g_k+s_k)\to0$ and $S_k(g_k+s_k)\to0$.
--
--   The vector $2(A;S)(g+s)$ is the gradient of the infeasibility measure $(x,s)\mapsto\|g(x)+s\|^2$, so the iterates approach its stationary points.
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`. The open set is not assumed convex, as on the page.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 24, Lemma 4.5

import Mathlib
import Definitions.Def_BarrierTR_Global_AlgorithmI
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Lemma 4.5 (p. 24). For a run of Algorithm I, if `{g_k}`, `{A_k}`, `{B_k}` are bounded, `{f_k}` is
bounded below, and `g`, `A`, `∇f` are Lipschitz continuous on an open set containing all the
iterates, then `(A_k; S_k)(g_k + s_k) → 0`, i.e. `A_k(g_k + s_k) → 0` and `S_k(g_k + s_k) → 0`. -/
theorem lemma_4_5 {n m : ℕ} (f : E n → ℝ) (g : E n → F m) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (P : Params n m) (R : RunData n m) (hR : IsRun P f g R)
    (hgb : ∃ C, ∀ k, ‖g (R.x k)‖ ≤ C) (hAb : ∃ C, ∀ k, ‖A g (R.x k)‖ ≤ C)
    (hBb : ∃ C, ∀ k, ‖R.B k‖ ≤ C) (hfb : BddBelow (Set.range fun k => f (R.x k)))
    (Ω : Set (E n)) (hΩ : IsOpen Ω) (hxΩ : ∀ k, R.x k ∈ Ω)
    (hLg : LipOn Ω g) (hLA : LipOn Ω (A g)) (hLf : LipOn Ω (gradient f)) :
    Tendsto (fun k => A g (R.x k) (g (R.x k) + R.s k)) atTop (𝓝 0) ∧
      Tendsto (fun k => diagL (fun i => R.s k i) (g (R.x k) + R.s k)) atTop (𝓝 0) := by sorry

end BarrierTR.Global
