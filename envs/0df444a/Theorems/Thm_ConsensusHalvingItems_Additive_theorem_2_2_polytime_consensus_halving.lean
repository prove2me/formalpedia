-- Prove2me | Theorems.Thm_ConsensusHalvingItems_Additive_theorem_2_2_polytime_consensus_halving
-- name    : ConsensusHalvingItems.Additive.theorem_2_2_polytime_consensus_halving
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:42:04.75507+00:00
-- url     : https://prove2.me/theorems/a74e6564-8e16-4e8e-9edc-b38464126ca3
-- title:
--   Theorem 2.2: polynomial-time consensus halving with at most $\min\{n,m\}$ cuts
-- statement:
--   Let $n$ agents have additive utilities over $m$ items, given by the rational values $u_i(j)$. There is a polynomial-time algorithm that computes a consensus halving with at most $\min\{n, m\}$ cuts. Precisely, there are constants $C, k$ such that for every instance $u$ the algorithm of the paper, with output $x$ and running time $\mathrm{cost}$, satisfies
--
--   1. $(x, 1 - x)$ is a consensus halving: $0 \le x_j \le 1$ for every item $j$ and
--   $$
--   \sum_{j \in M} x_j \cdot u_i(j) = \sum_{j \in M} (1 - x_j) \cdot u_i(j) \qquad \forall i \in N;
--   $$
--   2. at most $\min\{n, m\}$ items are cut, i.e. $\#\{ j : 0 < x_j < 1 \} \le \min\{n, m\}$;
--   3. $\mathrm{cost} \le C (|u| + 1)^k$, where $|u|$ is the bit size of the input.
--
--   A consensus halving with at most $n$ cuts always exists; the theorem shows that for additive utilities one can be found efficiently, and that with fewer agents than items most items can be left uncut. The bound $\min\{n, m\}$ is attained by generic instances (Theorem 2.5 of the paper).
--
--   **Formalization Note** Running time is the tick count of the mission's bit-cost model: every rational operation is charged quadratically in the bit sizes of its operands and every input value read is charged its bit size. The constants $C, k$ do not depend on $n$, $m$ or $u$.
--
--   Differences from the source:
--   - reading: polynomial-time (no machine model fixed) → tick count of the bit-cost model (ticked rational operations charged (bitSize a + bitSize b + 1)², input reads charged bitSize) bounded by C·(inputSize + 1)^k with C, k chosen before n, m, u; reason: the standard bit model; a unit-cost reading would ignore number growth and be weaker (Reading 1)
--   - reading: real utilities ui(j) (no encoding fixed) → rational values u : Fin n → Fin m → ℚ; reason: an algorithm takes encoded input; reals have no finite encoding (Reading 2)
--   - encoding: the algorithm of Steps 1–4 with free choices (footnote 5's arbitrary non-pivot value, the argmin of Step 3b) → the definitions kernelDir / findSolution / loopStep / halve with the canonical kernel vector and lowest-index tie-break; reason: the paper leaves these choices open; any fixed choice is an instance of its algorithm, and the theorem's "there exists a polynomial-time algorithm" is witnessed by this algorithm itself (Reading 3)
--   - generalization: nonnegative utilities; N = [n], M = [m] for positive n, m → values of any sign; n = 0 and m = 0 allowed; reason: the p. 6 remark extends the algorithm to negative values; the statement specializes to nonnegative values and positive n, m
--   - encoding: partition (M1, M2) of the items M = [m]; agents N = [n] → (x, 1 − x) with x : Fin m → ℚ; 0-based Fin n, Fin m; reason: a two-part partition is determined by its first part; same instances
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Theorem 2.2, p. 4 (proof p. 5)

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_halve
import Definitions.Def_ConsensusHalvingItems_Additive_IsConsensusHalving
import Definitions.Def_ConsensusHalvingItems_Additive_numCuts
import Definitions.Def_ConsensusHalvingItems_Additive_inputSize

namespace ConsensusHalvingItems.Additive

/-- **Theorem 2.2.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, Theorem 2.2, p. 4: "For n agents with additive utilities, there exists
a polynomial-time algorithm that computes a consensus halving with at most min{n, m} cuts."

There are constants `C, k` such that for all `n, m` and every value matrix
`u : Fin n → Fin m → ℚ` (`u i j` = agent `i`'s value for item `j`; utilities additive), the run
of the algorithm `halve u` from tick `0`, with output `x` and final tick count `cost`,
satisfies

1. `(x, 1 - x)` is a consensus halving: every `x j ∈ [0, 1]` and every agent values both parts
   equally;
2. at most `min n m` items are cut;
3. `cost ≤ C * (inputSize u + 1) ^ k`.

**Formalization Note.** "Polynomial-time" is read in the bit model of `tick`: every rational
operation costs `opCost`, quadratic in the bit sizes of its operands, and every input value
read costs its bit size (Reading 1). The utilities are rationals (Reading 2), of any sign (the
p. 6 remark), and `n = 0`, `m = 0` are allowed (Reading 4). The algorithm is the paper's
Steps 1–4 with the choices of footnote 5 and Step 3(b) fixed (Reading 3). `C` and `k` are
chosen before `n`, `m` and `u`. The `+ 1` only matters when `inputSize u = 0`. -/
theorem theorem_2_2_polytime_consensus_halving :
    ∃ C k : ℕ, ∀ {n m : ℕ} (u : Fin n → Fin m → ℚ),
      IsConsensusHalving u ((halve u).run 0).1 ∧
      numCuts ((halve u).run 0).1 ≤ min n m ∧
      ((halve u).run 0).2 ≤ C * (inputSize u + 1) ^ k := by sorry

end ConsensusHalvingItems.Additive
