-- Prove2me | Theorems.Thm_BBBV_RandomPermutation_prob_membership_differs
-- name    : BBBV.RandomPermutation.prob_membership_differs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:22.720035+00:00
-- url     : https://prove2.me/theorems/e045f79b-8dfe-4617-94e5-c46f3f71551f
-- title:
--   Proof of Theorem 3.6 — consecutive language memberships differ with probability 1/2
-- statement:
--   For $n\ge1$ and $T\ge1$, compare the languages associated with $\pi_T$ and $\pi_{T-1}$ at the string $1^n$. Exactly one language contains $1^n$ precisely when the first bits of their two inverse images differ. Under the chain's uniform sample law,
--
--   $$\Pr\bigl[1^n\in\mathcal L_{\pi_T}\mathbin{\triangle}\mathcal L_{\pi_{T-1}}\bigr]=\frac12.$$
--
--   This is the membership split used to turn closeness of algorithmic states into a failure bound.
--
--   **Formalization Note** The first bit requires $n\ge1$ and the preceding permutation requires $T\ge1$.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 11, proof of Theorem 3.6, first paragraph

import Mathlib
import Definitions.Def_BBBV_RandomPermutation_Chain

namespace BBBV.RandomPermutation

theorem prob_membership_differs {n T : ℕ} (hn : 0 < n) (hT : 1 ≤ T) :
    ((Finset.univ.filter fun ω : Ω n T =>
      (firstBit hn ((piChain ω T).symm (BBBV.RandomOracle.ones n)) = 1) ↔
        ¬ (firstBit hn ((piChain ω (T - 1)).symm (BBBV.RandomOracle.ones n)) = 1)).card : ℝ) /
      (Fintype.card (Ω n T) : ℝ) = 1 / 2 := by sorry

end BBBV.RandomPermutation
