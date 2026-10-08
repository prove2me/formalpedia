-- Prove2me | Theorems.Thm_BarrierTR_Global_theorem_4_10
-- name    : BarrierTR.Global.theorem_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:10.402761+00:00
-- url     : https://prove2.me/theorems/56e13c0f-afbf-42b9-b610-15ac14d2a643
-- title:
--   Theorem 4.10, pp. 30–31 — if σ_min((A_kᵀ S_k)) is bounded away from 0: s_k bounded away from 0, g_k < 0 eventually, ∇f_k + μA_kS_k⁻¹e → 0
-- statement:
--   Consider a run of Algorithm I applied to the barrier problem (2.2) with barrier parameter $\mu$. Suppose that Assumptions 4.1 hold and that the singular values of the matrices $(A_k^\top\ S_k)$ are bounded away from zero. Then
--
--   1. $s_k$ is bounded away from zero and $g_k$ is negative for all large $k$;
--   2. $$\nabla f_k+\mu A_kS_k^{-1}e\to0.$$
--
--   Together with $g_k+s_k\to0$ this is asymptotic stationarity for (2.2) with multipliers $\lambda_k=\mu S_k^{-1}e$: outcome (iii) of Theorem 4.3.
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`. \"Bounded away from zero\" is read componentwise and for all $k$: $\exists c>0$ with $c\le s_k^{(i)}$ for all $k,i$; the singular value bound is $\exists\hat\sigma>0$ with $\hat\sigma\|w\|\le\|(A_kw,S_kw)\|$ for all $k,w$.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, pp. 30–31, Theorem 4.10

import Mathlib
import Definitions.Def_BarrierTR_Global_AlgorithmI
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Theorem 4.10 (pp. 30–31). For a run of Algorithm I under Assumptions 4.1 for which the singular
values of `(A_kᵀ S_k)` are bounded away from zero: (i) `s_k` is bounded away from zero and `g_k` is
negative for all large `k`; (ii) `∇f_k + μ A_k S_k⁻¹ e → 0`. -/
theorem theorem_4_10 {n m : ℕ} (f : E n → ℝ) (g : E n → F m) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (P : Params n m) (R : RunData n m) (hR : IsRun P f g R)
    (hA41 : Assumptions41 f g R)
    (hsv : ∃ σ : ℝ, 0 < σ ∧ ∀ k (w : F m), σ * ‖w‖ ≤ ‖stackAS g (R.x k) (R.s k) w‖) :
    ((∃ c : ℝ, 0 < c ∧ ∀ k i, c ≤ R.s k i) ∧ ∀ᶠ k in atTop, ∀ i, g (R.x k) i < 0) ∧
      Tendsto (fun k => gradient f (R.x k) + P.μ • A g (R.x k) (sInvE (R.s k)))
        atTop (𝓝 0) := by sorry

end BarrierTR.Global
