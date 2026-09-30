-- Prove2me | Theorems.Thm_AndersonAccel_Safe_run_H_bounds
-- name    : AndersonAccel.Safe.run_H_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:09:48.954408+00:00
-- url     : https://prove2.me/theorems/8288ab48-3d1c-4473-8f81-38b213b0a55d
-- title:
--   Corollary 3.5 — along Algorithm 3.1, (3.8) holds and $\mathrm{cond}(H_k)\le(3((1+\bar\theta+\tau)/\tau)^m-2)^n/\bar\theta^m$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$ be nonexpansive, $\|f(x)-f(y)\|_2\le\|x-y\|_2$, with a fixed point, and run Algorithm 3.1 with $\bar\theta,\tau,\alpha\in(0,1)$, $D,\epsilon>0$ and max-memory $m\ge1$. Suppose no iterate is a solution: $f(x^k)\ne x^k$ for all $k$. Then for every $k\ge0$ the matrix $H_k$ is invertible,
--   $$\|H_k\|_2\le\Bigl(3\Bigl(\frac{1+\bar\theta+\tau}{\tau}\Bigr)^m-2\Bigr)^{n-1}\Big/\bar\theta^{\,m},$$
--   and its condition number $\mathrm{cond}(H_k)=\|H_k\|_2\|H_k^{-1}\|_2$ satisfies
--   $$\mathrm{cond}(H_k)\le\Bigl(3\Bigl(\frac{1+\bar\theta+\tau}{\tau}\Bigr)^m-2\Bigr)^{n}\Big/\bar\theta^{\,m}.$$
--
--   This connects the window lemmas to the algorithm itself: the restart rule, the Powell regularization and nonexpansiveness of $f$ (hence $\|y_i\|_2\le 2\|s_i\|_2$) make every matrix the algorithm uses uniformly bounded and well conditioned.
--
--   **Formalization Note** "Unless a solution to (1.1) is found in finite steps" is the hypothesis $f(x^k)\ne x^k$ for all $k$. Invertibility of $H_k$ is stated explicitly because $\mathrm{cond}(H_k)$ presupposes it; the inverse is `Ring.inverse`. The algorithm is `IsAAISRun`, with line 9 as in Eq. (3.3) at a window start (see that definition); with the printed line 9 the paper's justification (p. 3179) does not cover the iterations with $m_k=1$.
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3179, Corollary 3.5

import Mathlib
import Definitions.Def_AndersonAccel_Safe_Basic
import Definitions.Def_AndersonAccel_Safe_IsAAISRun

namespace AndersonAccel.Safe

/-- Corollary 3.5 (p. 3179). Along Algorithm 3.1, unless a solution is found in finitely many
steps, every `H_k` is invertible, (3.8) holds, and `cond(H_k) = ‖H_k‖ ‖H_k⁻¹‖` is bounded by
`(3((1 + θ̄ + τ)/τ)^m - 2)^n / θ̄^m`. -/
theorem run_H_bounds {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LipschitzWith 1 f)
    (θbar τ α D ε : ℝ) (m : ℕ)
    (hθ0 : 0 < θbar) (hθ1 : θbar < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hD : 0 < D) (hε : 0 < ε) (hm : 0 < m)
    (x xt s y shat ytil : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (mem nAA : ℕ → ℕ)
    (hrun : IsAAISRun f θbar τ α D ε m x xt s y shat ytil H mem nAA)
    (hX : ∃ z, f z = z)
    (hnosol : ∀ k, f (x k) ≠ x k) :
    ∀ k, IsUnit (H k) ∧
      ‖H k‖ ≤ (3 * ((1 + θbar + τ) / τ) ^ m - 2) ^ (n - 1) / θbar ^ m ∧
      ‖H k‖ * ‖Ring.inverse (H k)‖ ≤ (3 * ((1 + θbar + τ) / τ) ^ m - 2) ^ n / θbar ^ m := by sorry

end AndersonAccel.Safe
