-- Prove2me | Theorems.Thm_BBBV_RandomOracle_prob_uniqueInverse_ge
-- name    : BBBV.RandomOracle.prob_uniqueInverse_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:51.299209+00:00
-- url     : https://prove2.me/theorems/f8b37809-aa4b-457d-af15-4942cc8b3991
-- title:
--   Proof of Theorem 3.5, p. 9 — 1ⁿ has a unique preimage under a random A with probability ((2ⁿ−1)/2ⁿ)^{2ⁿ−1} ≥ 1/e
-- statement:
--   Let $n \ge 0$ and let $A$ be chosen uniformly at random among all functions $\{0,1\}^n \to \{0,1\}^n$. The probability that $1^n$ has exactly one preimage under $A$ (that is, $A \in \mathcal{B}$) is
--   $$\Pr[A \in \mathcal{B}] = \left(\frac{2^n - 1}{2^n}\right)^{2^n - 1} \ge \frac1e .$$
--
--   The class $\mathcal{B}$ is where the proof of Theorem 3.5 locates the oracles on which the algorithm fails: an oracle of $\mathcal{A}$ with one answer changed to $1^n$ lies in $\mathcal{B}$.
--
--   **Formalization Note** The probability is the fraction of functions with the property; the exponent $2^n - 1$ is natural-number subtraction, which is exact since $2^n \ge 1$. The statement holds for every $n$, including $n = 0$ (both sides equal $1$).
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 9, proof of Theorem 3.5, third paragraph (the class ℬ)

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

namespace BBBV.RandomOracle

open Classical in
theorem prob_uniqueInverse_ge {n : ℕ} :
    ((Finset.univ.filter fun A : Str n → Str n => UniqueInverse A).card : ℝ) /
        (Fintype.card (Str n → Str n) : ℝ) = (((2 : ℝ) ^ n - 1) / 2 ^ n) ^ (2 ^ n - 1) ∧
      Real.exp (-1) ≤ (((2 : ℝ) ^ n - 1) / 2 ^ n) ^ (2 ^ n - 1) := by sorry

end BBBV.RandomOracle
