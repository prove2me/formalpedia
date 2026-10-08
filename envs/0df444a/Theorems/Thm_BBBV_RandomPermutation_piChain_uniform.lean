-- Prove2me | Theorems.Thm_BBBV_RandomPermutation_piChain_uniform
-- name    : BBBV.RandomPermutation.piChain_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:16.657987+00:00
-- url     : https://prove2.me/theorems/9d0af2e3-1376-44fc-9c72-121bac18f543
-- title:
--   Proof of Theorem 3.6 — each permutation in the transposition chain is uniform
-- statement:
--   In the transposition chain, for every index $0\le i\le T+1$, the permutation $\pi_i$ is uniformly distributed among all permutations of length-$n$ binary strings:
--
--   $$\Pr[\pi_i=\sigma]=\frac{1}{(2^n)!}\quad\text{for every permutation }\sigma.$$
--
--   The construction also satisfies $\pi_i(x_i)=1^n$ for every sampled outcome. These facts identify both the law of the oracle and the distinguished inverse image at each stage.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 10, proof of Theorem 3.6, transposition-chain paragraph

import Mathlib
import Definitions.Def_BBBV_RandomPermutation_Chain

namespace BBBV.RandomPermutation

theorem piChain_uniform {n T : ℕ} (i : ℕ) (hi : i ≤ T + 1)
    (σ : Equiv.Perm (BBBV.RandomOracle.Str n)) :
    (((Finset.univ.filter fun ω : Ω n T => piChain ω i = σ).card : ℝ) /
      (Fintype.card (Ω n T) : ℝ) =
        1 / (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ)) ∧
    (∀ ω : Ω n T, piChain ω i (x ω i) = BBBV.RandomOracle.ones n) := by sorry

end BBBV.RandomPermutation
