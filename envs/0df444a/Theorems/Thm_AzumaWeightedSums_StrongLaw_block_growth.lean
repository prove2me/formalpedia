-- Prove2me | Theorems.Thm_AzumaWeightedSums_StrongLaw_block_growth
-- name    : AzumaWeightedSums.StrongLaw.block_growth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:25:44.490759+00:00
-- url     : https://prove2.me/theorems/9817455d-e86b-47d7-9a2d-b8c150f53850
-- title:
--   Proof of Theorem 3 — $A_{n_k} > (2(3+\varepsilon)/(6+\varepsilon))^{k-1}$ from (4.11), (4.12), (4.14)
-- statement:
--   Let $(a_n)_{n\ge1}$ be positive, $A_n=a_1+\dots+a_n$, $\varepsilon>0$, and let $(n_k)_{k\ge1}$ be natural numbers satisfying
--
--   1. (4.11) $A_{n_1} > 2(3+\varepsilon)/(6+\varepsilon)$;
--   2. (4.12) $a_n/A_n < \varepsilon/(6+\varepsilon)$ for all $n>n_1$;
--   3. (4.14) $A_{n_{k-1}} < A_{n_k} \le (1+\varepsilon/3)A_{n_{k-1}} < A_{n_k+1}$ for every $k\ge2$.
--
--   Then
--
--   $$A_{n_k} > \Big(\frac{2(3+\varepsilon)}{6+\varepsilon}\Big)^{k-1}, \qquad k=1,2,\dots$$
--
--   Since $2(3+\varepsilon)/(6+\varepsilon)>1$, the block totals $A_{n_k}$ grow at least geometrically. Combined with (4.13) and (4.16), this makes the series $\sum_k P\{\max_{n_k<n\le n_{k+1}}\bar S_n>\varepsilon A_{n_k}\}$ converge, so the Borel–Cantelli lemma applies.
--
--   **Formalization Note** The sequence $(n_k)$ is indexed by $k\ge1$; its value at $k=0$ is unused. Monotonicity of $(n_k)$ is not assumed; it follows from (4.14) and the positivity of $(a_n)$.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), p. 366, proof of Theorem 3 (display following (4.16))

import Mathlib
import Definitions.Def_AzumaWeightedSums_StrongLaw_ReversedSum

namespace AzumaWeightedSums.StrongLaw

/-- Growth of the blocks in the proof of Theorem 3 (Azuma 1967, p. 366): if `(a_n)` is positive,
`ε > 0`, and `(n_k)_{k ≥ 1}` satisfies (4.11) `A_{n_1} > 2(3+ε)/(6+ε)`,
(4.12) `a_n/A_n < ε/(6+ε)` for `n > n_1`, and
(4.14) `A_{n_{k-1}} < A_{n_k} ≤ (1 + ε/3) A_{n_{k-1}} < A_{n_k + 1}` for `k ≥ 2`, then
`A_{n_k} > (2(3+ε)/(6+ε))^{k-1}` for `k = 1, 2, …`. -/
theorem block_growth (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ε : ℝ) (hε : 0 < ε) (nk : ℕ → ℕ)
    (h411 : 2 * (3 + ε) / (6 + ε) < A a (nk 1))
    (h412 : ∀ n : ℕ, nk 1 < n → a n / A a n < ε / (6 + ε))
    (h414 : ∀ k : ℕ, 2 ≤ k →
        A a (nk (k - 1)) < A a (nk k) ∧ A a (nk k) ≤ (1 + ε / 3) * A a (nk (k - 1)) ∧
          (1 + ε / 3) * A a (nk (k - 1)) < A a (nk k + 1)) :
    ∀ k : ℕ, 1 ≤ k → (2 * (3 + ε) / (6 + ε)) ^ (k - 1) < A a (nk k) := by sorry

end AzumaWeightedSums.StrongLaw
