-- Prove2me | Theorems.Thm_FedergruenZipkin_AvgCost_lemma2c_sum_growth
-- name    : FedergruenZipkin.AvgCost.lemma2c_sum_growth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:19:24.269329+00:00
-- url     : https://prove2.me/theorems/d39cda3a-d18f-4706-a04a-9cdb3015e1eb
-- title:
--   Lemma 2(c) (p. 197) — $\sum_j j^r e^{-j^\beta/(a\sqrt t)} = O(t^{\lambda/2})$, $\lambda = (r+1)/\beta$
-- statement:
--   Let $r, \beta, a$ be real numbers with $r \ge 0$ and $a, \beta > 0$. For $j = 0, 1, \dots$ and $t = 1, 2, \dots$ put
--   $$n_j(t) = j^r \exp\Bigl(-\frac{j^\beta}{a\sqrt t}\Bigr),\qquad \lambda = \frac{r+1}{\beta}.$$
--   Then $\sum_{j=0}^\infty n_j(t) = O(t^{\lambda/2})$: there is a constant $C$ (depending on $r, \beta, a$) such that for every integer $t \ge 1$ the series converges and
--   $$\sum_{j=0}^{\infty} n_j(t) \le C\, t^{\lambda/2}.$$
--
--   This growth bound is one of the estimates used in the proof of Lemma 3.
--
--   **Formalization Note** The printed $\exp(-j^\beta/a\sqrt t)$ is read as $\exp(-j^\beta/(a\sqrt t))$, as the proof's function $f(z) = z^r\exp(-z^\beta/a\sqrt t)$ and its maximizer $\gamma = (ra\sqrt t/\beta)^{1/\beta}$ confirm. Powers are real powers, with $0^0 = 1$. Convergence is stated explicitly so that a divergent series cannot satisfy the bound vacuously.
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I, Math. Oper. Res. 11(2), 1986, p. 197, Lemma 2(c)

import Mathlib

namespace FedergruenZipkin.AvgCost
theorem lemma2c_sum_growth (r β a : ℝ) (hr : 0 ≤ r) (ha : 0 < a) (hβ : 0 < β) :
    ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t →
      Summable (fun j : ℕ => (j : ℝ) ^ r * Real.exp (-((j : ℝ) ^ β) / (a * Real.sqrt t))) ∧
        ∑' j : ℕ, (j : ℝ) ^ r * Real.exp (-((j : ℝ) ^ β) / (a * Real.sqrt t)) ≤
          C * (t : ℝ) ^ (((r + 1) / β) / 2) := by sorry
end FedergruenZipkin.AvgCost
