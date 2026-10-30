-- Prove2me | Theorems.Thm_ConsensusHalvingItems_Additive_reachable_step_polytime
-- name    : ConsensusHalvingItems.Additive.reachable_step_polytime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:37:53.184219+00:00
-- url     : https://prove2.me/theorems/bf4b12e9-61c0-4707-91f1-59a29c432429
-- title:
--   Proof of Theorem 2.2: the other steps run in polynomial time
-- statement:
--   There are constants $C, k$ such that for every instance $u$ with $n$ agents and $m$ items and every state $(T, x)$ reached by the while loop of the algorithm:
--
--   1. every entry $x_j$ has bit size at most $C(|u| + 1)^k$;
--   2. one iteration of Step 3 from $(T, x)$ (the test, followed by Steps 3a–3d) runs in time at most $C(|u| + 1)^k$,
--
--   where $|u|$ is the input size. This makes precise the paper's sentence "Moreover, it is obvious that the other steps of the algorithm run in polynomial time."
--
--   **Formalization Note** In the bit-cost model the cost of an arithmetic operation grows with its operands, so the claim includes that the iterates stay polynomially small (clause 1), which the paper leaves implicit.
--
--   Differences from the source:
--   - reading: polynomial-time (no machine model fixed) → tick count of the bit-cost model (ticked rational operations charged (bitSize a + bitSize b + 1)², input reads charged bitSize) bounded by C·(inputSize + 1)^k with C, k chosen before n, m, u; reason: the standard bit model; a unit-cost reading would ignore number growth and be weaker (Reading 1)
--   - reading: real utilities ui(j) (no encoding fixed) → rational values u : Fin n → Fin m → ℚ; reason: an algorithm takes encoded input; reals have no finite encoding (Reading 2)
--   - encoding: the algorithm of Steps 1–4 with free choices (footnote 5's arbitrary non-pivot value, the argmin of Step 3b) → the definitions kernelDir / findSolution / loopStep / halve with the canonical kernel vector and lowest-index tie-break; reason: the paper leaves these choices open; any fixed choice is an instance of its algorithm (Reading 3)
--   - reading: "it is obvious that the other steps of the algorithm run in polynomial time" → a polynomial bound on the bit size of every entry of every loop state and on the cost of one iteration from it; reason: in the bit model these are what the sentence asserts; the iteration count is bounded separately (≤ m iterations)
--   - generalization: nonnegative utilities; N = [n], M = [m] for positive n, m → values of any sign; n = 0 and m = 0 allowed; reason: the p. 6 remark extends the algorithm to negative values; the statement specializes to nonnegative values and positive n, m
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, proof of Theorem 2.2, ¶2, p. 5

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_Reachable
import Definitions.Def_ConsensusHalvingItems_Additive_bitSize
import Definitions.Def_ConsensusHalvingItems_Additive_inputSize

namespace ConsensusHalvingItems.Additive

/-- **The other steps run in polynomial time.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, proof of Theorem 2.2, ¶2, p. 5: "Moreover, it is obvious that the
other steps of the algorithm run in polynomial time."

There are constants `C, k` such that for all `n, m`, every value matrix `u` and every state
`(T, x)` reached by the loop of the algorithm:

1. every entry of `x` has bit size at most `C * (inputSize u + 1) ^ k`;
2. one iteration `loopStep u T x` (Step 3's test followed by Steps 3(a)–(d)), run from any start
   value `t` of the counter, ends with counter at most `t + C * (inputSize u + 1) ^ k`.

**Formalization Note.** Bit model of `tick` (Reading 1): the cost of an arithmetic operation
grows with the size of its operands, so the paper's "obvious" includes that the iterates stay
polynomially small; clause 1 makes this explicit. The statement is about the states the algorithm
constructs (`Reachable`), not about arbitrary `(T, x)`. -/
theorem reachable_step_polytime :
    ∃ C k : ℕ, ∀ {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ),
      Reachable u (T, x) →
        (∀ j, bitSize (x j) ≤ C * (inputSize u + 1) ^ k) ∧
        ∀ t, ((loopStep u T x).run t).2 ≤ t + C * (inputSize u + 1) ^ k := by sorry

end ConsensusHalvingItems.Additive
