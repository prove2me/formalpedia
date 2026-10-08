-- Prove2me | Theorems.Thm_BarrierTR_Global_lemma_4_6
-- name    : BarrierTR.Global.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:19.054087+00:00
-- url     : https://prove2.me/theorems/3da99b00-e773-4967-a28a-cd33219cdb09
-- title:
--   Lemma 4.6, p. 26 — A_k g_k⁺ → 0, and ν_k → ∞ unless the iterates are asymptotically feasible
-- statement:
--   Under the conditions of Lemma 4.5 (a run of Algorithm I with $\{g_k\},\{A_k\},\{B_k\}$ bounded, $\{f_k\}$ bounded below, and $g$, $A$, $\nabla f$ Lipschitz on an open set containing the iterates),
--   $$A_k\,g_k^+\to0,$$
--   where $(u^+)^{(i)}=\max(0,u^{(i)})$. Moreover, if the sequence of iterates is not asymptotically feasible, i.e. if $g_k^+\not\to0$, then the penalty parameters $\nu_k$ tend to infinity.
--
--   $2A(x)g(x)^+$ is the gradient of $\|g(x)^+\|^2$, so the iterates approach stationarity of the measure of infeasibility of (2.1); this is outcome (i) of Theorem 4.3.
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 26, Lemma 4.6

import Mathlib
import Definitions.Def_BarrierTR_Global_AlgorithmI
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Lemma 4.6 (p. 26). Under the conditions of Lemma 4.5, `A_k g_k⁺ → 0`; moreover, if the iterates
are not asymptotically feasible (`g_k⁺ ↛ 0`), then the penalty parameters `ν_k` tend to infinity. -/
theorem lemma_4_6 {n m : ℕ} (f : E n → ℝ) (g : E n → F m) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (P : Params n m) (R : RunData n m) (hR : IsRun P f g R)
    (hgb : ∃ C, ∀ k, ‖g (R.x k)‖ ≤ C) (hAb : ∃ C, ∀ k, ‖A g (R.x k)‖ ≤ C)
    (hBb : ∃ C, ∀ k, ‖R.B k‖ ≤ C) (hfb : BddBelow (Set.range fun k => f (R.x k)))
    (Ω : Set (E n)) (hΩ : IsOpen Ω) (hxΩ : ∀ k, R.x k ∈ Ω)
    (hLg : LipOn Ω g) (hLA : LipOn Ω (A g)) (hLf : LipOn Ω (gradient f)) :
    Tendsto (fun k => A g (R.x k) (pos (g (R.x k)))) atTop (𝓝 0) ∧
      (¬ IsAsymptoticallyFeasible g R.x → Tendsto R.ν atTop atTop) := by sorry

end BarrierTR.Global
