-- Prove2me | Theorems.Thm_BarrierTR_Global_lemma_4_8
-- name    : BarrierTR.Global.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:20.03414+00:00
-- url     : https://prove2.me/theorems/450a25ec-ea1c-40f9-ac00-f2aad8e2f5be
-- title:
--   Lemma 4.8, p. 27 — if σ_min((A_kᵀ S_k)) ≥ σ̂ > 0, then ‖g_k+s_k‖ ≤ γ₃ ⟹ ‖(v_x; S_k⁻¹v_s)‖ ≤ γ₄ vpred_k
-- statement:
--   Consider a run of Algorithm I applied to (2.2), and suppose that Assumptions 4.1 hold and that for some $\hat\sigma>0$
--   $$\sigma_{\min}\big((A_k^\top\ S_k)\big)\ge\hat\sigma>0\qquad(4.16)$$
--   for all $k$. Then there are positive constants $\gamma_3$ and $\gamma_4$ such that if $\|g_k+s_k\|\le\gamma_3$, the accepted vertical step $v_k=(v_x,v_s)$ satisfies
--   $$\Big\|\binom{v_x}{S_k^{-1}v_s}\Big\|\le\gamma_4\,\mathrm{vpred}_k(v_k).\qquad(4.17)$$
--
--   Bounding the vertical step by its own predicted reduction is what keeps the penalty parameter bounded in Lemma 4.9.
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 27, Lemma 4.8, (4.16)–(4.17)

import Mathlib
import Definitions.Def_BarrierTR_Global_AlgorithmI
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Lemma 4.8 (p. 27). For a run of Algorithm I under Assumptions 4.1, if
`σ_min((A_kᵀ S_k)) ≥ σ̂ > 0` for all `k` (4.16), there are `γ₃, γ₄ > 0` such that
`‖g_k + s_k‖ ≤ γ₃` implies `‖(v_x; S_k⁻¹v_s)‖ ≤ γ₄ vpred_k(v_k)` (4.17). -/
theorem lemma_4_8 {n m : ℕ} (f : E n → ℝ) (g : E n → F m) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (P : Params n m) (R : RunData n m) (hR : IsRun P f g R)
    (hA41 : Assumptions41 f g R) (σ : ℝ) (hσ : 0 < σ)
    (hsv : ∀ k (w : F m), σ * ‖w‖ ≤ ‖stackAS g (R.x k) (R.s k) w‖) :
    ∃ γ₃ γ₄ : ℝ, 0 < γ₃ ∧ 0 < γ₄ ∧ ∀ k, ‖g (R.x k) + R.s k‖ ≤ γ₃ →
      ‖pair (R.v k).fst (diagL (fun i => 1 / R.s k i) (R.v k).snd)‖
        ≤ γ₄ * vpred g (R.x k) (R.s k) (R.v k) := by sorry

end BarrierTR.Global
