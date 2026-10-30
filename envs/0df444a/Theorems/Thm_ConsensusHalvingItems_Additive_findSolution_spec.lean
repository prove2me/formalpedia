-- Prove2me | Theorems.Thm_ConsensusHalvingItems_Additive_findSolution_spec
-- name    : ConsensusHalvingItems.Additive.findSolution_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:37:00.610587+00:00
-- url     : https://prove2.me/theorems/ec59e0f2-425b-42af-8cf0-b5b2f41a62f7
-- title:
--   Proof of Theorem 2.2: Step 3 by Gaussian elimination, in polynomial time
-- statement:
--   There are constants $C, k$ such that for every instance $u$ with $n$ agents and $m$ items, every set $T$ of items and every point $x \in \mathbb{Q}^m$, the test of Step 3 (Gaussian elimination on the system $S \cup T$, as in footnote 5):
--
--   1. runs in time at most
--   $$
--   C \Bigl(|u| + \sum_{j} \operatorname{bitSize}(x_j) + 1\Bigr)^k ,
--   $$
--   where $|u|$ is the input size;
--   2. if $x$ solves $S$, either returns a solution $y \ne x$ of $S \cup T$, or reports that none exists, and it reports that none exists exactly when $x$ is the unique solution of $S \cup T$.
--
--   This is the paper's claim that "finding a solution $(y_1, \dots, y_m)$ to $S \cup T$ that is not equal to $(x_1, \dots, x_m)$ or determining that such a solution does not exist (Step 3) can be done in polynomial time via Gaussian elimination".
--
--   **Formalization Note** The time bound counts the size of the current point $x$, an input of Step 3; along the algorithm this size is bounded by the next milestone. The cost bound rests on the classical fact that the numbers produced by Gaussian elimination over the rationals have polynomially bounded bit size, which the paper uses implicitly.
--
--   Differences from the source:
--   - reading: polynomial-time (no machine model fixed) → tick count of the bit-cost model (ticked rational operations charged (bitSize a + bitSize b + 1)², input reads charged bitSize) bounded by C·(inputSize + 1)^k with C, k chosen before n, m, u; reason: the standard bit model; a unit-cost reading would ignore number growth and be weaker (Reading 1)
--   - reading: real utilities ui(j) (no encoding fixed) → rational values u : Fin n → Fin m → ℚ; reason: an algorithm takes encoded input; reals have no finite encoding (Reading 2)
--   - encoding: the algorithm of Steps 1–4 with free choices (footnote 5's arbitrary non-pivot value, the argmin of Step 3b) → the definitions kernelDir / findSolution / loopStep / halve with the canonical kernel vector and lowest-index tie-break; reason: the paper leaves these choices open; any fixed choice is an instance of its algorithm (Reading 3)
--   - generalization: Step 3 for the pairs (T, x) met by the algorithm, with x solving S ∪ T → every T and every x (the cost bound unconditionally; correctness for every x solving S, T arbitrary); reason: the algorithm's states satisfy these hypotheses, so the statement specializes to the paper's
--   - generalization: nonnegative utilities; N = [n], M = [m] for positive n, m → values of any sign; n = 0 and m = 0 allowed; reason: the p. 6 remark extends the algorithm to negative values; the statement specializes to nonnegative values and positive n, m
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, ¶2, p. 5, and footnote 5, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_findSolution
import Definitions.Def_ConsensusHalvingItems_Additive_SolvesST
import Definitions.Def_ConsensusHalvingItems_Additive_inputSize

namespace ConsensusHalvingItems.Additive

/-- **Step 3's test runs in polynomial time and is correct.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, ¶2, p. 5: "Finding a solution (y1, . . . , ym) to
S ∪ T that is not equal to (x1, . . . , xm) or determining that such a solution does not exist
(Step 3) can be done in polynomial time via Gaussian elimination." Footnote 5, p. 5:
"Specifically, if the linear equations in S ∪ T lead to a unique solution (x1, . . . , xm), then
Gaussian elimination immediately results in this solution. Otherwise, Gaussian elimination will
yield a row echelon form; by setting one of the non-pivots yj to be an arbitrary number not equal
to xj, we obtain a solution that is not equal to (x1, . . . , xm)."

There are constants `C, k` (independent of everything below) such that for all `n, m`, every
value matrix `u`, every `T ⊆ Fin m`, every point `x` and every start value `t` of the tick
counter:

1. (cost) the run of `findSolution u T x` ends with counter at most
   `t + C * (inputSize u + ∑_j bitSize (x j) + 1) ^ k`;
2. (correctness) if `x` solves S, then every returned `some y` is a solution of S ∪ T with
   `y ≠ x`, and the result is `none` exactly when `x` is the unique solution of S ∪ T.

**Formalization Note.** Bit-cost model of `tick` (Reading 1). The size of `x` appears in the
bound because `x` is an input of this step; along the algorithm it is bounded by milestone
`reachable_step_polytime`. The cost bound needs the classical fact (Edmonds) that the entries met
by Gaussian elimination over ℚ have polynomially bounded bit size; the paper leaves it implicit. -/
theorem findSolution_spec :
    ∃ C k : ℕ, ∀ {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ) (t : ℕ),
      ((findSolution u T x).run t).2 ≤ t + C * (inputSize u + ∑ j, bitSize (x j) + 1) ^ k ∧
      (SolvesS u x →
        (∀ y, ((findSolution u T x).run t).1 = some y → y ≠ x ∧ SolvesST u T x y) ∧
        (((findSolution u T x).run t).1 = none ↔ ∀ y, SolvesST u T x y → y = x)) := by sorry

end ConsensusHalvingItems.Additive
