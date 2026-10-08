-- Prove2me | Theorems.Thm_BarrierTR_Global_lemma_4_9
-- name    : BarrierTR.Global.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:18.646193+00:00
-- url     : https://prove2.me/theorems/26864051-ae67-42bd-b850-1e6be66841f2
-- title:
--   Lemma 4.9, p. 30 — under (4.17) for large k, ν_k is bounded and eventually constant, and pred_k(d_k) ≥ γ₅ hpred_k
-- statement:
--   Consider a run of Algorithm I applied to (2.2). Suppose that Assumptions 4.1 are satisfied, and that (4.17) holds for $k$ sufficiently large: for some $\gamma_4>0$ and all large $k$, $\|(v_x;S_k^{-1}v_s)\|\le\gamma_4\,\mathrm{vpred}_k(v_k)$. Then the sequence of penalty parameters $\{\nu_k\}$ is bounded. In addition, there exist an index $k_1$ and positive scalars $\bar\nu$ and $\gamma_5$ such that for all $k\ge k_1$,
--   $$\nu_k=\bar\nu\qquad\text{and}\qquad\mathrm{pred}_k(d_k)\ge\gamma_5\,\mathrm{hpred}_k(h_k).\qquad(4.26)$$
--
--   With a fixed penalty the merit function decreases monotonically, which Theorem 4.10 exploits.
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 30, Lemma 4.9, (4.26)

import Mathlib
import Definitions.Def_BarrierTR_Global_AlgorithmI
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Lemma 4.9 (p. 30). For a run of Algorithm I under Assumptions 4.1 for which (4.17)
`‖(v_x; S_k⁻¹v_s)‖ ≤ γ₄ vpred_k` holds for all sufficiently large `k`, the penalty parameters `{ν_k}` are
bounded, and there are an index `k₁` and `ν̄, γ₅ > 0` with `ν_k = ν̄` and
`pred_k(d_k) ≥ γ₅ hpred_k(h_k)` (4.26) for all `k ≥ k₁`. -/
theorem lemma_4_9 {n m : ℕ} (f : E n → ℝ) (g : E n → F m) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (P : Params n m) (R : RunData n m) (hR : IsRun P f g R)
    (hA41 : Assumptions41 f g R)
    (h417 : ∃ γ₄ : ℝ, 0 < γ₄ ∧ ∀ᶠ k in atTop,
      ‖pair (R.v k).fst (diagL (fun i => 1 / R.s k i) (R.v k).snd)‖
        ≤ γ₄ * vpred g (R.x k) (R.s k) (R.v k)) :
    (∃ C, ∀ k, |R.ν k| ≤ C) ∧
      ∃ (k₁ : ℕ) (νbar γ₅ : ℝ), 0 < νbar ∧ 0 < γ₅ ∧ ∀ k ≥ k₁, R.ν k = νbar ∧
        γ₅ * hpred f P.μ (R.x k) (R.s k) (R.B k) (R.v k) (R.h k)
          ≤ pred f g P.μ (R.ν k) (R.x k) (R.s k) (R.B k) (R.d k) := by sorry

end BarrierTR.Global
