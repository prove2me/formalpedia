-- Prove2me | Theorems.Thm_BarrierTR_Global_lemma_4_4
-- name    : BarrierTR.Global.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:17.297371+00:00
-- url     : https://prove2.me/theorems/9ae852c2-d2d6-4847-8572-d3daeea4cb22
-- title:
--   Lemma 4.4, p. 22 — {f_k} bounded below and {g_k} bounded ⟹ {s_k} bounded and {φ(x_k,s_k;ν_k)} bounded below
-- statement:
--   Consider a run of Algorithm I applied to the barrier problem (2.2), with iterates $(x_k,s_k)$ and penalty parameters $\nu_k$. Assume that $\{f(x_k)\}$ is bounded below and that $\{g(x_k)\}$ is bounded. Then the sequence $\{s_k\}$ is bounded, and consequently
--   $$\{\phi(x_k,s_k;\nu_k)\}\ \text{is bounded below.}$$
--
--   The slack bound replaces a compactness assumption in the rest of §4.
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 22, Lemma 4.4

import Mathlib
import Definitions.Def_BarrierTR_Global_AlgorithmI
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Lemma 4.4 (p. 22). For a run of Algorithm I, if `{f_k}` is bounded below and `{g_k}` is bounded,
then `{s_k}` is bounded, and `{φ(x_k, s_k; ν_k)}` is bounded below. -/
theorem lemma_4_4 {n m : ℕ} (f : E n → ℝ) (g : E n → F m) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (P : Params n m) (R : RunData n m) (hR : IsRun P f g R)
    (hfb : BddBelow (Set.range fun k => f (R.x k))) (hgb : ∃ C, ∀ k, ‖g (R.x k)‖ ≤ C) :
    (∃ C, ∀ k, ‖R.s k‖ ≤ C) ∧
      BddBelow (Set.range fun k => merit f g P.μ (R.ν k) (R.x k) (R.s k)) := by sorry

end BarrierTR.Global
