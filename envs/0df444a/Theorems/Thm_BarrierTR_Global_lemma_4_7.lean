-- Prove2me | Theorems.Thm_BarrierTR_Global_lemma_4_7
-- name    : BarrierTR.Global.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:09.727045+00:00
-- url     : https://prove2.me/theorems/b8803649-a1e7-4023-a757-93ad890be24f
-- title:
--   Lemma 4.7, p. 27 — if g_k + s_k → 0: σ_min((A_kᵀ S_k)) ≥ σ̂ > 0 for all k, or a limit point fails LICQ and ν_k → ∞
-- statement:
--   Consider a run of Algorithm I applied to (2.2). Suppose that the sequences $\{g_k\}$ and $\{A_k\}$ are bounded, and that $g_k+s_k\to0$. Then either there is some bound $\hat\sigma>0$ such that
--   $$\sigma_{\min}\big((A_k^\top\ S_k)\big)\ge\hat\sigma\quad\text{for all }k,$$
--   or the sequence $\{(g_k,A_k)\}$ has a limit point $(\bar g,\bar A)$ failing the linear independence constraint qualification. In the latter case, the penalty parameter $\nu_k$ goes to infinity.
--
--   This separates outcomes (ii) and (iii) of Theorem 4.3.
--
--   **Formalization Note** "Smooth" (p. 1) is read as $C^1$: $f$ and $g$ are continuously differentiable on all of $\mathbb R^n$. Vectors live in `EuclideanSpace`, stacked vectors $(a,b)$ in `WithLp 2` products, so every $\|\cdot\|$ is the Euclidean norm (spectral norm for matrices). $A(x)$ is the adjoint of the derivative of $g$, so $A(x)^\top d_x$ is `fderiv ℝ g x d_x`. $\sigma_{\min}((A_k^\top\ S_k))\ge\hat\sigma$ is written as $\hat\sigma\|w\|\le\|(A_kw,S_kw)\|$ for all $w\in\mathbb R^m$. **Added hypothesis:** $\{f_k\}$ is bounded below. The page does not list it, but the proof uses it twice: through Lemma 4.4 and in the claim that $-\ln s_k^{(i)}\to\infty$ is incompatible with the decrease of $\phi$ at a fixed penalty.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 27, Lemma 4.7

import Mathlib
import Definitions.Def_BarrierTR_Global_AlgorithmI
open scoped RealInnerProductSpace
open Filter Topology

namespace BarrierTR.Global

/-- Lemma 4.7 (p. 27). For a run of Algorithm I with `{g_k}`, `{A_k}` bounded and `g_k + s_k → 0`
(and `{f_k}` bounded below, used by the proof through Lemma 4.4): either
`σ_min((A_kᵀ S_k)) ≥ σ̂` for all `k`, for some `σ̂ > 0`, or `{(g_k, A_k)}` has a limit point failing the
linear independence constraint qualification; in the latter case `ν_k → ∞`. -/
theorem lemma_4_7 {n m : ℕ} (f : E n → ℝ) (g : E n → F m) (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (P : Params n m) (R : RunData n m) (hR : IsRun P f g R)
    (hgb : ∃ C, ∀ k, ‖g (R.x k)‖ ≤ C) (hAb : ∃ C, ∀ k, ‖A g (R.x k)‖ ≤ C)
    (hfeas : Tendsto (fun k => g (R.x k) + R.s k) atTop (𝓝 0))
    (hfb : BddBelow (Set.range fun k => f (R.x k))) :
    ((∃ σ : ℝ, 0 < σ ∧ ∀ k (w : F m), σ * ‖w‖ ≤ ‖stackAS g (R.x k) (R.s k) w‖) ∨
        HasLICQFailingLimitPoint g R.x) ∧
      (HasLICQFailingLimitPoint g R.x → Tendsto R.ν atTop atTop) := by sorry

end BarrierTR.Global
