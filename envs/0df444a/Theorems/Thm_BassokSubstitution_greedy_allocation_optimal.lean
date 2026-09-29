-- Prove2me | Theorems.Thm_BassokSubstitution_greedy_allocation_optimal
-- name    : BassokSubstitution.greedy_allocation_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T08:18:30.95908+00:00
-- url     : https://prove2.me/theorems/91ed59e0-226c-44f9-94c9-1e0439bc6ee8
-- title:
--   Proposition 1 — the greedy allocation algorithm (A) solves the allocation LP
-- statement:
--   Consider the single-period $N$-product model with downward substitution, satisfying Assumptions 1–3 and with nonnegative substitution cost $b \ge 0$. Let $y \ge 0$ be the stock levels after ordering and $d \ge 0$ the realized demands, and let $(w^A, u^A, v^A)$ be the allocation produced by Allocation Algorithm (A). Then:
--
--   1. $(w^A, u^A, v^A)$ is feasible for the allocation LP (3);
--   2. its objective is at least the objective of every feasible allocation;
--   3. its objective equals $G(y,d)$:
--   $$\sum_{i=1}^N \sum_{j=1}^{i} a_{ji} w^A_{ji} + \sum_{i=1}^N s_i v^A_i - \sum_{i=1}^N \pi_i u^A_i = G(y,d).$$
--
--   This makes the second-stage profit explicit: every later statement about $P$ is proved by analysing the greedy allocation instead of a linear program.
--
--   **Formalization Note.** The hypothesis $b \ge 0$ is used by the paper without being stated ($b$ is introduced as a *cost* of substitution). It is needed: with $b < 0$, serving a class from a more flexible product and salvaging the class's own product can beat the greedy allocation.
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 634, Proposition 1

import Mathlib
import Definitions.Def_BassokSubstitution_Allocation

namespace BassokSubstitution

/-- Proposition 1: under Assumptions 1–3 (and a nonnegative substitution cost), for any
nonnegative stock vector `y` and demand vector `d`, the allocation produced by Algorithm (A)
is feasible for the allocation LP (3), its objective is at least that of every feasible
allocation, and it equals `G(y, d)`. -/
theorem greedy_allocation_optimal {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (y d : Fin N → ℝ) (hy : 0 ≤ y) (hd : 0 ≤ d) :
    (greedyAllocation y d).Feasible y d ∧
      (∀ a : Allocation N, a.Feasible y d →
        M.allocObjective a ≤ M.allocObjective (greedyAllocation y d)) ∧
      M.allocObjective (greedyAllocation y d) = M.G y d := by sorry

end BassokSubstitution
