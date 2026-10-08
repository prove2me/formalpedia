-- Prove2me | Theorems.Thm_BBBV_RandomPermutation_theorem_3_6
-- name    : BBBV.RandomPermutation.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:52.851996+00:00
-- url     : https://prove2.me/theorems/4cd3e138-3dda-4fc9-befa-7d0327a6c735
-- title:
--   Theorem 3.6 — random permutation query lower bound for the first inverse bit
-- statement:
--   Let $n\ge1$, and let $M$ be any finite-dimensional quantum query algorithm making $T$ queries to a permutation of the length-$n$ binary strings. For a permutation $A$, ask whether the first bit of $A^{-1}(1^n)$ is $1$. If $T\le 2^{n/3}/100$, then
--
--   $$\Pr_{A\text{ uniform}}[M\text{ does not decide this bit with error at most }1/3]\ge\frac18.$$
--
--   The probability is over all $(2^n)!$ permutations; the algorithm and its finite workspace are fixed before the permutation is sampled. This is the finite-length lower bound in the proof of the paper's almost-sure oracle separation.
--
--   **Formalization Note** The statement uses the query model rather than a full oracle quantum Turing machine. Answers at lengths other than $n$ are fixed and absorbed into the inter-query unitaries. The hypothesis $n\ge1$ makes the first bit defined. The paper's constants $1/100$ and $1/8$ are kept. The almost-sure statement over countably many machines is outside this mission's Lean goal. One full-value oracle query can be simulated by $n$ Boolean queries, while one Boolean query can be simulated by two full-value queries, so the lower bound transfers to the paper's Boolean oracle with a constant adjustment.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 10, Theorem 3.6 and finite claim (proof pp. 10–12)

import Mathlib
import Definitions.Def_BBBV_RandomPermutation_Chain

namespace BBBV.RandomPermutation

open Classical

theorem theorem_3_6 (n : ℕ) (hn : 0 < n) (W : Type) [Fintype W] (T : ℕ)
    (hT : (T : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 3) / 100)
    (M : QueryAlg (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W T) :
    (1 / 8 : ℝ) ≤
      ((Finset.univ.filter fun A : Equiv.Perm (BBBV.RandomOracle.Str n) =>
          ¬ Decides M (fun _ => ⇑A) (firstBit hn (A.symm (BBBV.RandomOracle.ones n)) = 1)).card : ℝ) /
        (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ) := by sorry

end BBBV.RandomPermutation
