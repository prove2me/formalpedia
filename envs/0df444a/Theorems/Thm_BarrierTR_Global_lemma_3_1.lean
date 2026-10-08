-- Prove2me | Theorems.Thm_BarrierTR_Global_lemma_3_1
-- name    : BarrierTR.Global.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:00:53.481411+00:00
-- url     : https://prove2.me/theorems/d32e0164-5f21-433d-be8a-89ca2679b53c
-- title:
--   Lemma 3.1, p. 18 — |pred_k(d) − ared_k(d)| ≤ γ_L((1+ν_k)‖d_x‖² + ‖S_k⁻¹d_s‖²)
-- statement:
--   Consider a run of Algorithm I with iterates $(x_k,s_k)$, penalties $\nu_k$ and matrices $B_k$. Suppose that $\nabla f$ and $A$ are Lipschitz continuous on an open convex set $X$ containing all the iterates $\{x_k\}$, and that $\{B_k\}$ is bounded. Then there is a constant $\gamma_L>0$ such that for any iterate $(x_k,s_k)$ and any step $d=(d_x,d_s)$ such that the segment $[x_k,x_k+d_x]$ lies in $X$, $s_k>0$ and $d_s\ge-\tau s_k$,
--   $$|\mathrm{pred}_k(d)-\mathrm{ared}_k(d)|\ \le\ \gamma_L\big((1+\nu_k)\|d_x\|^2+\|S_k^{-1}d_s\|^2\big).$$
--
--   The model $m_k$ is thus an accurate local model of the merit function, which is how step acceptance is controlled in §3–§4.
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`. $\mathrm{pred}_k$ and $\mathrm{ared}_k$ use the run's $\nu_k$, $B_k$ and $\mu$; $d$ is an arbitrary step, not necessarily the algorithm's.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 18, Lemma 3.1

import Mathlib
import Definitions.Def_BarrierTR_Global_AlgorithmI
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Lemma 3.1 (p. 18). If `∇f` and `A` are Lipschitz continuous on an open convex set `X` containing
all iterates `{x_k}` of Algorithm I and `{B_k}` is bounded, there is `γ_L > 0` such that for any iterate
`(x_k, s_k)` and step `d = (d_x, d_s)` with `[x_k, x_k + d_x] ⊆ X`, `s_k > 0` and `d_s ≥ −τ s_k`,
`|pred_k(d) − ared_k(d)| ≤ γ_L((1 + ν_k)‖d_x‖² + ‖S_k⁻¹d_s‖²)`. -/
theorem lemma_3_1 {n m : ℕ} (f : E n → ℝ) (g : E n → F m) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (P : Params n m) (R : RunData n m) (hR : IsRun P f g R)
    (X : Set (E n)) (hXo : IsOpen X) (hXc : Convex ℝ X) (hX : ∀ k, R.x k ∈ X)
    (hLf : LipOn X (gradient f)) (hLA : LipOn X (A g)) (hB : ∃ C, ∀ k, ‖R.B k‖ ≤ C) :
    ∃ γL : ℝ, 0 < γL ∧ ∀ (k : ℕ) (d : Z n m),
      segment ℝ (R.x k) (R.x k + d.fst) ⊆ X → (∀ i, 0 < R.s k i) →
        (∀ i, -P.τ * R.s k i ≤ d.snd i) →
        |pred f g P.μ (R.ν k) (R.x k) (R.s k) (R.B k) d
            - ared f g P.μ (R.ν k) (R.x k) (R.s k) d|
          ≤ γL * ((1 + R.ν k) * ‖d.fst‖ ^ 2 + ‖diagL (fun i => 1 / R.s k i) d.snd‖ ^ 2) := by sorry

end BarrierTR.Global
