-- Prove2me | Theorems.Thm_AndersonAccel_Safe_dist_converges
-- name    : AndersonAccel.Safe.dist_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:12:32.167987+00:00
-- url     : https://prove2.me/theorems/ccab3057-353b-4ad2-929a-6faa72a7bcde
-- title:
--   Section 4.1, Step 2 — $\|x^k-y\|_2$ converges for every fixed point $y$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$ be nonexpansive and run Algorithm 3.1 with $\bar\theta,\tau,\alpha\in(0,1)$, $D,\epsilon>0$ and max-memory $m\ge1$, assuming no iterate is a solution ($f(x^k)\ne x^k$ for all $k$). Then for every fixed point $y=f(y)$ the distance $\|x^k-y\|_2$ converges: there is $L\in\mathbb R$ with
--   $$\lim_{k\to\infty}\|x^k-y\|_2=L.$$
--
--   Together with the vanishing residual (4.6), this is the Opial-type ingredient from which convergence of the whole sequence follows.
--
--   **Formalization Note** The hypothesis $f(x^k)\ne x^k$ is the paper's standing simplification at the start of §4.1.
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3181, Section 4.1, Step 2

import Mathlib
import Definitions.Def_AndersonAccel_Safe_Basic
import Definitions.Def_AndersonAccel_Safe_IsAAISRun

namespace AndersonAccel.Safe

open Filter Topology

/-- Section 4.1, Step 2 (p. 3181). For every fixed point `y` of `f`, `‖x^k - y‖` converges. -/
theorem dist_converges {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LipschitzWith 1 f)
    (θbar τ α D ε : ℝ) (m : ℕ)
    (hθ0 : 0 < θbar) (hθ1 : θbar < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hD : 0 < D) (hε : 0 < ε) (hm : 0 < m)
    (x xt s y shat ytil : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (mem nAA : ℕ → ℕ)
    (hrun : IsAAISRun f θbar τ α D ε m x xt s y shat ytil H mem nAA)
    (hnosol : ∀ k, f (x k) ≠ x k)
    (yf : EuclideanSpace ℝ (Fin n)) (hyf : f yf = yf) :
    ∃ L : ℝ, Tendsto (fun k => ‖x k - yf‖) atTop (𝓝 L) := by sorry

end AndersonAccel.Safe
