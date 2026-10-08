-- Prove2me | Theorems.Thm_FedergruenZipkin_AvgCost_lemma2b_sum_bound
-- name    : FedergruenZipkin.AvgCost.lemma2b_sum_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:19:11.116949+00:00
-- url     : https://prove2.me/theorems/74d022da-e90a-4394-bc15-015a862f5f33
-- title:
--   Lemma 2(b) (p. 196) — a bound on $\sum_{t>k} (t^2+rt)/(t-a)^4$
-- statement:
--   Let $a, r \ge 0$ be real numbers and $k$ an integer with $k > a$. Then the series below converges and
--   $$\sum_{t=k+1}^{\infty} \frac{t^2 + rt}{(t-a)^4} \le \frac{1}{k-a} + \frac{r + 2a}{2(k-a)^2} + \frac{ra + a^2}{3(k-a)^3}.$$
--
--   This estimate controls the tail sums that appear in the proof of Lemma 3.
--
--   **Formalization Note** The sum is indexed by $t = k + 1 + n$, $n = 0, 1, \dots$. Convergence of the series is stated explicitly, so that a divergent series (whose Lean `tsum` would be $0$) cannot satisfy the bound vacuously. The proof on p. 197 evaluates the last integral as $\tfrac13(ra - a^2)(k-a)^{-3}$, a misprint; the statement's $ra + a^2$ is used here.
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I, Math. Oper. Res. 11(2), 1986, p. 196, Lemma 2(b)

import Mathlib

namespace FedergruenZipkin.AvgCost
theorem lemma2b_sum_bound (a r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (k : ℤ) (hk : a < k) :
    Summable (fun n : ℕ => (((k : ℝ) + 1 + n) ^ 2 + r * ((k : ℝ) + 1 + n)) /
        ((k : ℝ) + 1 + n - a) ^ 4) ∧
      ∑' n : ℕ, (((k : ℝ) + 1 + n) ^ 2 + r * ((k : ℝ) + 1 + n)) / ((k : ℝ) + 1 + n - a) ^ 4 ≤
        1 / ((k : ℝ) - a) + (r + 2 * a) / (2 * ((k : ℝ) - a) ^ 2) +
          (r * a + a ^ 2) / (3 * ((k : ℝ) - a) ^ 3) := by sorry
end FedergruenZipkin.AvgCost
