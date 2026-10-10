-- Prove2me | Theorems.Thm_BBBV_RandomOracle_prob_noInverse_ge
-- name    : BBBV.RandomOracle.prob_noInverse_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T16:55:47.310107+00:00
-- url     : https://prove2.me/theorems/2854e8f1-68e9-47d4-9553-c423c4eb2451
-- title:
--   Proof of Theorem 3.5, p. 9 — a uniformly random A : {0,1}ⁿ → {0,1}ⁿ misses 1ⁿ with probability ((2ⁿ−1)/2ⁿ)^{2ⁿ} ≥ 1/4
-- statement:
--   Let $n \ge 1$ and let $A$ be chosen uniformly at random among all $(2^n)^{2^n}$ functions $\{0,1\}^n \to \{0,1\}^n$. The probability that $1^n$ has no preimage under $A$ (that is, $A \in \mathcal{A}$) is
--   $$\Pr[A \in \mathcal{A}] = \left(\frac{2^n - 1}{2^n}\right)^{2^n} \ge \frac14 .$$
--
--   This is the mass of the class $\mathcal{A}$ in the proof of Theorem 3.5: the final failure probability $1/8$ is half of it.
--
--   **Formalization Note** The probability is the fraction of functions with the property. The paper writes "at least $1/4$ (for $n$ sufficiently large)"; the bound holds for every $n \ge 1$, with equality at $n = 1$, and is stated so.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 9, proof of Theorem 3.5, third paragraph (the class 𝒜)

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

namespace BBBV.RandomOracle

open Classical in
theorem prob_noInverse_ge {n : ℕ} (hn : 1 ≤ n) :
    ((Finset.univ.filter fun A : Str n → Str n => NoInverse A).card : ℝ) /
        (Fintype.card (Str n → Str n) : ℝ) = (((2 : ℝ) ^ n - 1) / 2 ^ n) ^ (2 ^ n) ∧
      (1 / 4 : ℝ) ≤ (((2 : ℝ) ^ n - 1) / 2 ^ n) ^ (2 ^ n) := by sorry

end BBBV.RandomOracle
