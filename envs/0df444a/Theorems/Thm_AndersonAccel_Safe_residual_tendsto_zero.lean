-- Prove2me | Theorems.Thm_AndersonAccel_Safe_residual_tendsto_zero
-- name    : AndersonAccel.Safe.residual_tendsto_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:11:14.676877+00:00
-- url     : https://prove2.me/theorems/7b8deeb4-c577-4152-a6ba-c6d5c37cda0b
-- title:
--   Eq. (4.6) — the residuals of Algorithm 3.1 tend to zero
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$ be nonexpansive with a nonempty fixed-point set, and run Algorithm 3.1 with $\bar\theta,\tau,\alpha\in(0,1)$, $D,\epsilon>0$ and max-memory $m\ge1$, assuming no iterate is a solution ($f(x^k)\ne x^k$ for all $k$). Then the residuals $g_k=x^k-f(x^k)$ satisfy
--   $$\lim_{k\to\infty}\|g_k\|_2=0.$$
--
--   This is Step 1 of the global convergence proof: both the averaged steps and the accepted accelerated steps drive the residual to zero.
--
--   **Formalization Note** The hypothesis $f(x^k)\ne x^k$ is the paper's standing simplification at the start of §4.1.
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3181, Section 4.1, Step 1, Eq. (4.6)

import Mathlib
import Definitions.Def_AndersonAccel_Safe_Basic
import Definitions.Def_AndersonAccel_Safe_IsAAISRun

namespace AndersonAccel.Safe

open Filter Topology

/-- Eq. (4.6) (p. 3181). The residuals of the iterates of Algorithm 3.1 tend to zero:
`lim_{k → ∞} ‖g_k‖ = 0`. -/
theorem residual_tendsto_zero {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LipschitzWith 1 f)
    (θbar τ α D ε : ℝ) (m : ℕ)
    (hθ0 : 0 < θbar) (hθ1 : θbar < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hD : 0 < D) (hε : 0 < ε) (hm : 0 < m)
    (x xt s y shat ytil : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (mem nAA : ℕ → ℕ)
    (hrun : IsAAISRun f θbar τ α D ε m x xt s y shat ytil H mem nAA)
    (hX : ∃ z, f z = z)
    (hnosol : ∀ k, f (x k) ≠ x k) :
    Tendsto (fun k => ‖residual f (x k)‖) atTop (𝓝 0) := by sorry

end AndersonAccel.Safe
