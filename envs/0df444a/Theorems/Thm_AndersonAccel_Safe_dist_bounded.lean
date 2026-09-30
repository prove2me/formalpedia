-- Prove2me | Theorems.Thm_AndersonAccel_Safe_dist_bounded
-- name    : AndersonAccel.Safe.dist_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:10:54.822977+00:00
-- url     : https://prove2.me/theorems/103128f9-95a5-4ac1-933f-83a4f5ff3c1f
-- title:
--   Eq. (4.3) — the iterates stay within $\|x^0-y\|_2+CD\bar U\sum_i(i+1)^{-(1+\epsilon)}$ of every fixed point
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$ be nonexpansive and run Algorithm 3.1 with $\bar\theta,\tau,\alpha\in(0,1)$, $D,\epsilon>0$ and max-memory $m\ge1$, assuming no iterate is a solution ($f(x^k)\ne x^k$ for all $k$). Let $y$ be any fixed point of $f$, $\bar U=\|g(x^0)\|_2$, and
--   $$C=\Bigl(3\Bigl(\frac{1+\bar\theta+\tau}{\tau}\Bigr)^m-2\Bigr)^{n-1}\Big/\bar\theta^{\,m}$$
--   the bound (3.8). Then for every $k\ge0$
--   $$\|x^k-y\|_2\ \le\ \|x^0-y\|_2+CD\bar U\sum_{i=0}^\infty(i+1)^{-(1+\epsilon)}.$$
--
--   In particular the iterates are bounded. The right-hand side is the constant $E$ of the paper.
--
--   **Formalization Note** The paper writes "some constant $C$ independent of the iteration count" with $\|H_{k_i}\|_2\le C$ by Corollary 3.5; the explicit bound (3.8) is used for $C$. The series is the `tsum` of $(i+1)^{-(1+\epsilon)}$ (real power), which converges since $\epsilon>0$. The hypothesis $f(x^k)\ne x^k$ is the paper's standing simplification at the start of §4.1.
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3180, Section 4.1, Step 1, Eq. (4.3)

import Mathlib
import Definitions.Def_AndersonAccel_Safe_Basic
import Definitions.Def_AndersonAccel_Safe_IsAAISRun

namespace AndersonAccel.Safe

/-- Eq. (4.3) (p. 3180). For every fixed point `y`,
`‖x^k - y‖ ≤ ‖x^0 - y‖ + C D Ū ∑_{i ≥ 0} (i + 1)^{-(1+ε)}` for all `k`, where `C` is the bound (3.8). -/
theorem dist_bounded {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LipschitzWith 1 f)
    (θbar τ α D ε : ℝ) (m : ℕ)
    (hθ0 : 0 < θbar) (hθ1 : θbar < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hD : 0 < D) (hε : 0 < ε) (hm : 0 < m)
    (x xt s y shat ytil : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (mem nAA : ℕ → ℕ)
    (hrun : IsAAISRun f θbar τ α D ε m x xt s y shat ytil H mem nAA)
    (hnosol : ∀ k, f (x k) ≠ x k)
    (yf : EuclideanSpace ℝ (Fin n)) (hyf : f yf = yf) :
    ∀ k, ‖x k - yf‖ ≤ ‖x 0 - yf‖ +
      (3 * ((1 + θbar + τ) / τ) ^ m - 2) ^ (n - 1) / θbar ^ m * D * ‖residual f (x 0)‖ *
        ∑' i : ℕ, ((i : ℝ) + 1) ^ (-(1 + ε)) := by sorry

end AndersonAccel.Safe
