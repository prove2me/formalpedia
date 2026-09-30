-- Prove2me | Theorems.Thm_AndersonAccel_Safe_norm_inverse_windowB_le
-- name    : AndersonAccel.Safe.norm_inverse_windowB_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:08:49.913344+00:00
-- url     : https://prove2.me/theorems/d285cb63-4a74-4149-8f67-1b724bbec0fe
-- title:
--   Corollary 3.4 — $\|H_k\|_2\le(3((1+\bar\theta+\tau)/\tau)^m-2)^{n-1}/\bar\theta^m$ (3.8)
-- statement:
--   Under the assumptions of Lemma 3.3 ($\bar\theta,\tau\in(0,1)$, max-memory $m\ge1$, $m_k\le m$, well-defined updates, $\|y_i\|_2\le2\|s_i\|_2$ and $\|\hat s_i\|_2\ge\tau\|s_i\|_2$ on the window), the inverse $H_k=B_k^{-1}$ of the Powell-regularized matrix satisfies
--   $$\|H_k\|_2\ \le\ \Bigl(3\Bigl(\frac{1+\bar\theta+\tau}{\tau}\Bigr)^m-2\Bigr)^{n-1}\Big/\bar\theta^{\,m}.\qquad(3.8)$$
--
--   This is the uniform bound on the approximate inverse Jacobians that the global convergence proof needs for every accelerated step.
--
--   **Formalization Note** $H_k$ is `Ring.inverse` of the window matrix, which is its true inverse by Lemma 3.2. $n$ is the dimension; for $n=0$ the natural-number subtraction gives $n-1=0$, which is harmless since then $H_k=0$.
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3178, Corollary 3.4, Eq. (3.8)

import Mathlib
import Definitions.Def_AndersonAccel_Safe_Basic
import Definitions.Def_AndersonAccel_Safe_windowB

namespace AndersonAccel.Safe

/-- Corollary 3.4, Eq. (3.8) (p. 3178). Under the hypotheses of Lemma 3.3,
`‖H‖ = ‖B⁻¹‖ ≤ (3((1 + θ̄ + τ)/τ)^m - 2)^{n-1} / θ̄^m`. -/
theorem norm_inverse_windowB_le {n : ℕ} (θbar τ : ℝ) (m : ℕ) (hθ0 : 0 < θbar) (hθ1 : θbar < 1)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hm : 1 ≤ m)
    (s y : ℕ → EuclideanSpace ℝ (Fin n)) (mk : ℕ) (hmk : mk ≤ m)
    (hwd : ∀ i < mk, inner ℝ (windowShat s i) (s i) ≠ 0)
    (hy : ∀ i < mk, ‖y i‖ ≤ 2 * ‖s i‖)
    (hτs : ∀ i < mk, τ * ‖s i‖ ≤ ‖windowShat s i‖) :
    ‖Ring.inverse (windowB θbar s y mk)‖ ≤
      (3 * ((1 + θbar + τ) / τ) ^ m - 2) ^ (n - 1) / θbar ^ m := by sorry

end AndersonAccel.Safe
