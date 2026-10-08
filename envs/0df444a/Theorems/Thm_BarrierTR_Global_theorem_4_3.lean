-- Prove2me | Theorems.Thm_BarrierTR_Global_theorem_4_3
-- name    : BarrierTR.Global.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:37.287119+00:00
-- url     : https://prove2.me/theorems/8fc1a86f-dc2f-4f1d-a642-73e200c8c73d
-- title:
--   Theorem 4.3, pp. 21–22 — Algorithm I: {s_k} bounded, (A_k;S_k)(g_k+s_k) → 0, and infeasible-stationary, LICQ-failing, or barrier-stationary
-- statement:
--   Suppose that Algorithm I is applied to the barrier problem (2.2) and that Assumptions 4.1 hold. Then
--
--   1. the sequence of slack variables $\{s_k\}$ is bounded;
--   2. $A_k(g_k+s_k)\to0$ and $S_k(g_k+s_k)\to0$.
--
--   Furthermore, one of the following three situations occurs.
--
--   - **(i)** $\{x_k\}$ is not asymptotically feasible. The iterates approach stationarity of the measure of infeasibility $x\mapsto\|g(x)^+\|$, meaning $A_kg_k^+\to0$, and the penalty parameters $\nu_k$ tend to infinity.
--   - **(ii)** $\{x_k\}$ is asymptotically feasible, but $\{(g_k,A_k)\}$ has a limit point $(\bar g,\bar A)$ failing the linear independence constraint qualification. The penalty parameters $\nu_k$ tend to infinity.
--   - **(iii)** $\{x_k\}$ is asymptotically feasible and all limit points of $\{(g_k,A_k)\}$ satisfy the linear independence constraint qualification. Then $\{s_k\}$ is bounded away from zero, $\nu_k$ is constant and $g_k$ is negative for all large $k$, and stationarity of (2.2) is obtained:
--   $$\nabla f_k+A_k\lambda_k\to0,\qquad\lambda_k=\mu S_k^{-1}e.$$
--
--   This is the paper's main convergence result for a fixed barrier parameter (restated as Theorem 4.11, p. 33).
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`. Each situation is a conjunction of its defining premise and its conclusions, and the theorem asserts the disjunction (i) ∨ (ii) ∨ (iii); since the premises of (ii) and (iii) are complementary, this is the printed case analysis. \"$\nu_k$ constant for all large $k$\" is $\exists\bar\nu$ with $\nu_k=\bar\nu$ eventually.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, pp. 21–22, Theorem 4.3 (= Theorem 4.11, p. 33)

import Mathlib
import Definitions.Def_BarrierTR_Global_AlgorithmI
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Theorem 4.3 (pp. 21–22; restated as Theorem 4.11, p. 33). For a run of Algorithm I applied to
the barrier problem (2.2) under Assumptions 4.1: 1) `{s_k}` is bounded; 2) `A_k(g_k + s_k) → 0` and
`S_k(g_k + s_k) → 0`; and one of the following occurs:
(i) `{x_k}` is not asymptotically feasible, `A_k g_k⁺ → 0` and `ν_k → ∞`;
(ii) `{x_k}` is asymptotically feasible, `{(g_k, A_k)}` has a limit point failing the LICQ, and
`ν_k → ∞`;
(iii) `{x_k}` is asymptotically feasible, all limit points of `{(g_k, A_k)}` satisfy the LICQ, `{s_k}`
is bounded away from zero, `ν_k` is constant and `g_k < 0` for all large `k`, and
`∇f_k + A_k λ_k → 0` with `λ_k = μ S_k⁻¹ e`. -/
theorem theorem_4_3 {n m : ℕ} (f : E n → ℝ) (g : E n → F m) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (P : Params n m) (R : RunData n m) (hR : IsRun P f g R)
    (hA41 : Assumptions41 f g R) :
    (∃ C, ∀ k, ‖R.s k‖ ≤ C) ∧
    Tendsto (fun k => A g (R.x k) (g (R.x k) + R.s k)) atTop (𝓝 0) ∧
    Tendsto (fun k => diagL (fun i => R.s k i) (g (R.x k) + R.s k)) atTop (𝓝 0) ∧
    ((¬ IsAsymptoticallyFeasible g R.x ∧
        Tendsto (fun k => A g (R.x k) (pos (g (R.x k)))) atTop (𝓝 0) ∧
        Tendsto R.ν atTop atTop) ∨
      (IsAsymptoticallyFeasible g R.x ∧ HasLICQFailingLimitPoint g R.x ∧
        Tendsto R.ν atTop atTop) ∨
      (IsAsymptoticallyFeasible g R.x ∧ ¬ HasLICQFailingLimitPoint g R.x ∧
        (∃ c : ℝ, 0 < c ∧ ∀ k i, c ≤ R.s k i) ∧
        (∃ νbar : ℝ, ∀ᶠ k in atTop, R.ν k = νbar) ∧
        (∀ᶠ k in atTop, ∀ i, g (R.x k) i < 0) ∧
        Tendsto (fun k => gradient f (R.x k) + A g (R.x k) (P.μ • sInvE (R.s k)))
          atTop (𝓝 0))) := by sorry

end BarrierTR.Global
