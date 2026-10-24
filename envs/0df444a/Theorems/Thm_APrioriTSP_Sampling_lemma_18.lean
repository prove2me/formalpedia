-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_lemma_18
-- name    : APrioriTSP.Sampling.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:27.736177+00:00
-- url     : https://prove2.me/theorems/d8fd49d5-6597-4095-8ca4-2e1ff09007cc
-- title:
--   Lemma 18, p. 14 — the tail Σ_{k=n+1}^∞ k·q^{k−1} = q^n/(1 − q)²·(1 + n − qn)
-- statement:
--   Let $n \in \mathbb N$ (including $n = 0$) and $q \in (0,1)$. Then the series $\sum_{k=n+1}^\infty k\,q^{k-1}$ converges, and
--   $$\sum_{k=n+1}^\infty k\cdot q^{k-1} = \frac{q^n}{(1-q)^2}\cdot(1 + n - qn) .$$
--
--   This closed form evaluates the tail of the linear bound $B_k \le k B_1$ against the weights $e^{-(k-1)\sigma\beta}$ in the proof of Lemma 14, with $n = N$ and $q = e^{-\sigma\beta}$; it produces the constant $\delta_2$.
--
--   **Formalization Note** The statement is `HasSum` of the sequence that is $k q^{k-1}$ for $k \ge n+1$ and $0$ otherwise, which asserts convergence as well as the value. Here $qn$ is the product $q\cdot n$.
--
--   Differences from the source:
--
--   - encoding: the equation Σ_{k=n+1}^∞ k·q^{k−1} = q^n/(1 − q)²·(1 + n − qn) → `HasSum` of k ↦ (if n + 1 ≤ k then k·q^{k−1} else 0) with that value; reason: states convergence and the value at once; ℕ subtraction k − 1 is exact for k ≥ n + 1 ≥ 1
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 14, Lemma 18, Equation (21)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting

namespace APrioriTSP.Sampling

/-- Lemma 18 (p. 14): `Σ_{k=n+1}^∞ k q^{k−1} = q^n / (1 − q)² · (1 + n − q n)` for `n ∈ ℕ`,
`q ∈ (0, 1)`. -/
theorem lemma_18 (n : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun k : ℕ => if n + 1 ≤ k then (k : ℝ) * q ^ (k - 1) else 0)
      (q ^ n / (1 - q) ^ 2 * (1 + n - q * n)) := by sorry

end APrioriTSP.Sampling
