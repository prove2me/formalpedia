-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_lemma_6_2
-- name    : FiniteGroupTesting.LinearQuery.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:26:03.757898+00:00
-- url     : https://prove2.me/theorems/f0a2b4ae-7e24-4840-8e93-a3da95ce08d5
-- title:
--   Lemma 6.2 — Hidden-copy instances are one-sixth far
-- statement:
--   For all sufficiently large consecutive prime pairs $p<q$ with $q-p\le600$, put $H=(\mathbb F_p)^3\times(\mathbb F_q)^2$ and $n=p^2q^3$. Embed $H$ into the $n$ labels and write its addition on the square of its image. Every deterministic completion outside that square satisfies
--   $$\operatorname{dist}(*,\circ)\ge1/6$$
--   for every group operation $\circ$ on all $n$ labels. In particular every table in the source's NO distribution is $1/6$-far. The threshold on $p$ is uniform in the embedding, completion and comparison group.
--
--   Differences from the source:
--   - encoding: labels [n]={1,...,n} → Fin n with zero representing paper label 1; reason: bijective relabelling preserves all tables, distances and query policies
--   - generalization: constant outside completion equal to paper label 1 → every deterministic outside completion; reason: the proof lower-bounds disagreements inside the hidden image squared, independently of outside entries
--   - encoding: additive F_p and F_q coordinates → addition modulo p and q on Fin p and Fin q; reason: these are additive coordinate labellings of exactly the same prime fields
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 35, Lemma 6.2

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_TranscriptModel

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem lemma_6_2 :
    ∃ N : ℕ, ∀ p q : ℕ, N ≤ p → ConsecutivePrimes p q → q - p ≤ 600 →
      ∀ (f : PairH p q ↪ Fin (p ^ 2 * q ^ 3)) (outside : Table (p ^ 2 * q ^ 3)),
        Far (1/6 : ℝ) (encodedTable pairAddH f outside) := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
