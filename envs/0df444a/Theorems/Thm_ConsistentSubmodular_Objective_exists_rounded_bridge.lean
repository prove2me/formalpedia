-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_exists_rounded_bridge
-- name    : ConsistentSubmodular.Objective.exists_rounded_bridge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:00.168451+00:00
-- url     : https://prove2.me/theorems/aaa48885-b15f-4fd8-b4b0-ba488db522f1
-- title:
--   Uniform rounded bridge with pure endpoints
-- statement:
--   Let $f$ be a nonnegative monotone submodular function on subsets of $[n]$, let $A,B,Q\subseteq[n]$, $N,\kappa\in\mathbb N$ with $N>0$, and $V\in\mathbb R$ with $V\ge 0$. Write $h_N=8N^2\,(\lfloor\log_2(4(2N+1))\rfloor+1)$ (the forced-element reserve `bridgeHeavy N`). Assume $N>0$ and
--
--   $$|A|\le\kappa,\quad |B|\le\kappa,\quad f(A)\le V,\quad f(B)\le V,\quad V\le f(Q\cup A),\quad V\le f(Q\cup B).$$
--
--   Then there is an operation path $P$ (consecutive sets differ by at most one element) with $P_0=A$, $P_{P.\mathrm{length}}=B$, $P.\mathrm{length}\le 10\kappa$, and for every node $P_j$:
--
--   $$P_j\subseteq A\cup B,\qquad |P_j|\le \kappa+\frac{\kappa}{N}+h_N,\qquad \Big(\frac34-\frac2N\Big)V\le f(Q\cup P_j).$$
--
--   The statement has no assumption relating $\kappa$ and $N$. The operation bound $10\kappa$ is independent of all instance sizes, and the additive cardinality overhead $\kappa/N+h_N$ depends only on $N$. The path links two sets that each have value at most $V$ but reach $V$ after adding the buffer $Q$, while keeping a $(3/4-2/N)$ fraction of $V$ at every step.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/BridgeRounding.lean#L213-L246 (`ConsistentSubmodular.Objective.exists_rounded_bridge`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_BridgeRounding

open scoped BigOperators
open ConsistentSubmodular
set_option maxHeartbeats 2000000
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.exists_rounded_bridge (A B Q : Finset (Fin n)) (N κ : ℕ) (V : ℝ)
    (hN : 0 < N) (hV : 0 ≤ V)
    (hAc : A.card ≤ κ) (hBc : B.card ≤ κ) (hAv : f.value A ≤ V) (hBv : f.value B ≤ V)
    (hA : V ≤ f.value (Q ∪ A)) (hB : V ≤ f.value (Q ∪ B)) :
    ∃ P : SetOperationPath n, P.node 0 = A ∧ P.node P.length = B ∧ P.length ≤ 10 * κ ∧
      ∀ j, P.node j ⊆ A ∪ B ∧ ((P.node j).card : ℝ) ≤ κ + (κ : ℝ) / N + bridgeHeavy N ∧
        ((3 : ℝ) / 4 - 2 / N) * V ≤ f.value (Q ∪ P.node j) := by sorry
