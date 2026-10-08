-- Prove2me | Theorems.Thm_AzumaWeightedSums_StrongLaw_block_sequence_exists
-- name    : AzumaWeightedSums.StrongLaw.block_sequence_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:06:31.326693+00:00
-- url     : https://prove2.me/theorems/22e216a2-fd02-43a6-8e79-6855a15bc9cf
-- title:
--   (4.11)–(4.14) — the block indices $n_1 < n_2 < \cdots$ of the proof of Theorem 3
-- statement:
--   Let $(a_n)_{n\ge1}$ be positive and nondecreasing, $A_n = a_1+\dots+a_n$, and suppose
--
--   $$\frac{a_n}{A_n} = o\Big(\frac{1}{\log\log A_n}\Big) \qquad (n\to\infty). \tag{4.9}$$
--
--   Then for every $\varepsilon>0$ there is a strictly increasing sequence of positive integers $n_1<n_2<\cdots$ such that
--
--   1. (4.11) $A_{n_1} > 2(3+\varepsilon)/(6+\varepsilon)$;
--   2. (4.12) $a_n/A_n < \varepsilon/(6+\varepsilon)$ for all $n>n_1$;
--   3. (4.13) $a_n(\log\log A_n)/A_n < \varepsilon^2/64$ for all $n>n_1$;
--   4. (4.14) $A_{n_{k-1}} < A_{n_k} \le (1+\varepsilon/3)A_{n_{k-1}} < A_{n_k+1}$ for every $k\ge2$.
--
--   These are the blocks along which the proof of Theorem 3 applies the Borel–Cantelli lemma: by (4.14), $A$ grows by a factor of at most $1+\varepsilon/3$ across a block, and $n_k$ is the last index at which it has not yet exceeded that factor.
--
--   **Formalization Note** The sequence is indexed by $k\ge1$; its value at $k=0$ is unconstrained. Condition (4.9) is stated literally as a little-$o$ relation (Mathlib's `IsLittleO` along `atTop`), with $1/\log\log A_n$ computed in Lean's real arithmetic; since $A_n\to\infty$ this function is eventually positive, so the relation is the paper's. No upper bound on $\varepsilon$ is assumed, as in the paper.
-- source:
--   Azuma, Weighted sums of certain dependent random variables, Tôhoku Math. J. 19 (1967), pp. 364–365, proof of Theorem 3, (4.11)–(4.14)

import Mathlib
import Definitions.Def_AzumaWeightedSums_StrongLaw_ReversedSum

namespace AzumaWeightedSums.StrongLaw

open Filter Asymptotics

/-- The choice of the blocks `(n_k)` in the proof of Theorem 3 (Azuma 1967, (4.11)–(4.14),
pp. 364–365): for positive nondecreasing weights satisfying (4.9) and every `ε > 0` there is a
strictly increasing sequence `(n_k)_{k ≥ 1}` of positive integers with
(4.11) `A_{n_1} > 2(3+ε)/(6+ε)`, (4.12) `a_n/A_n < ε/(6+ε)` and
(4.13) `a_n (log log A_n)/A_n < ε²/64` for `n > n_1`, and
(4.14) `A_{n_{k-1}} < A_{n_k} ≤ (1 + ε/3) A_{n_{k-1}} < A_{n_k + 1}` for `k ≥ 2`. -/
theorem block_sequence_exists (a : ℕ → ℝ) (ha_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n)
    (ha_mono : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1))
    (h49 : (fun n => a n / A a n) =o[atTop] (fun n => 1 / Real.log (Real.log (A a n))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ nk : ℕ → ℕ, (∀ k : ℕ, 1 ≤ k → 1 ≤ nk k ∧ nk k < nk (k + 1)) ∧
      2 * (3 + ε) / (6 + ε) < A a (nk 1) ∧
      (∀ n : ℕ, nk 1 < n → a n / A a n < ε / (6 + ε)) ∧
      (∀ n : ℕ, nk 1 < n → a n * Real.log (Real.log (A a n)) / A a n < ε ^ 2 / 64) ∧
      (∀ k : ℕ, 2 ≤ k →
        A a (nk (k - 1)) < A a (nk k) ∧ A a (nk k) ≤ (1 + ε / 3) * A a (nk (k - 1)) ∧
          (1 + ε / 3) * A a (nk (k - 1)) < A a (nk k + 1)) := by sorry

end AzumaWeightedSums.StrongLaw
