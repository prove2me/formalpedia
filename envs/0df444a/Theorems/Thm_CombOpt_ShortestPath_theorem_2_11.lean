-- Prove2me | Theorems.Thm_CombOpt_ShortestPath_theorem_2_11
-- name    : CombOpt.ShortestPath.theorem_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:05:59.037014+00:00
-- url     : https://prove2.me/theorems/69bdea7d-2e38-49dc-a825-99c43abd2ad5
-- title:
--   Theorem 2.11 — Ford's Algorithm terminates and its predecessors give least-cost dipaths
-- statement:
--   Let $G$ be a finite digraph with real arc costs $c$ and root $r$, and suppose $(G,c)$ has **no negative-cost dicircuit**.
--
--   1. **Termination.** Ford's Algorithm terminates after a finite number of iterations, whatever incorrect arc is corrected at each iteration: there is no infinite sequence of states, starting from the initialization, in which each state arises from the previous one by correcting an incorrect arc.
--   2. **Correctness.** Assume, as throughout the section, that every node $v$ is reachable from $r$ by a dipath. At termination (a reachable state with no incorrect arc) every label $y_v$ is a real number, $y$ is a feasible potential, and for each $v\in V$, $p$ defines a least-cost dipath from $r$ to $v$ of cost $y_v$.
--
--   Applied to a digraph with an added root joined to every node, this yields Theorem 2.12; its termination state gives the equality case of Proposition 2.9 used in Theorem 2.14.
--
--   Differences from the source:
--   - generalization: the section may assume G simple (p. 20) and p(w) stores the node v → loops and parallel arcs allowed, p(w) stores the corrected arc vw; reason: on a simple digraph the arc vw and its tail v determine each other, so the Lean statement specializes to the book's
--   - generalization: termination under the section's standing assumption that dipaths exist from r to every node (p. 20) → termination without that assumption; reason: the stronger statement implies the book's
--   - reading: "At termination, for each v ∈ V" under the section's standing assumption "we assume that dipaths exist from r to all the nodes" (p. 20) → the correctness part carries the hypothesis that every node is reachable from r; reason: the theorem relies on this standing assumption, and without it an unreachable v keeps y_v = ∞ and has no dipath
--   - reading: loop guard "while y is not a feasible potential" → an iteration exists exactly when some arc is incorrect, and terminal states are those with no incorrect arc; reason: the loop body needs an incorrect arc, and the conclusion asserts that every terminal reachable state carries a feasible potential, so both guards stop at the same states
--   - encoding: "terminates after a finite number of iterations" → no infinite sequence f with f 0 = fordInit r and FordStep (f n) (f (n+1)) for all n; reason: an execution is a sequence of iterations and the algorithm chooses the arc freely
--   - encoding: labels in ℝ ∪ {∞}, predecessor values 0 and −1 → WithTop ℝ with ⊤ = ∞, FordPred.root and FordPred.undef; reason: WithTop ℝ obeys the book's rules a + ∞ = ∞ and a < ∞
--   - encoding: a dipath is the sequence v_0, e_1, v_1, …, e_k, v_k → a start node and the arc list [e_1, …, e_k]; reason: the nodes are the start node and the heads of the arcs
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 2.11, p. 25 (PDF p. 34); standing assumption p. 20 (PDF p. 29); algorithm p. 22 (PDF p. 31)

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_HasNegativeDicircuit
import Definitions.Def_CombOpt_ShortestPath_Digraph_FordReachable
import Definitions.Def_CombOpt_ShortestPath_Digraph_PredDefinesDipath
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsLeastCostDipath
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsFeasiblePotential
import Definitions.Def_CombOpt_ShortestPath_pathCost

namespace CombOpt.ShortestPath

/-- **Theorem 2.11 (Ford's Algorithm terminates with least-cost dipaths).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 2.11, p. 25 (PDF p. 34): "If (G, c) has no negative-cost dicircuit, then Ford's
Algorithm terminates after a finite number of iterations. At termination, for each v ∈ V, p
defines a least-cost dipath from r to v of cost y_v."

Let `G` be a finite digraph with real arc costs `c`, root `r`, and no negative-cost
dicircuit.
1. *Termination:* there is no infinite execution: no sequence of states starting at
   `fordInit r` in which each state is obtained from the previous one by correcting an incorrect
   arc.
2. *Correctness:* assume (the section's standing assumption, p. 20, "we assume that dipaths exist
   from r to all the nodes") that every node is reachable from `r` by a dipath. Then at every
   reachable state `s` with no incorrect arc, the labels are real numbers `y v` forming a
   feasible potential, and for each node `v`, `s.p` defines a dipath from `r` to `v` that
   is a least-cost dipath and has cost `y v`.

**Formalization Note.** Termination is stated without the reachability assumption, which it
does not need. A state is terminal when no arc is incorrect; part 2 shows that this is exactly
the book's exit condition "y is a feasible potential". -/
theorem theorem_2_11 {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : Digraph V E)
    (c : E → ℝ) (r : V) (hc : ¬ G.HasNegativeDicircuit c) :
    (¬ ∃ f : ℕ → FordState V E, f 0 = fordInit r ∧ ∀ n : ℕ, G.FordStep c (f n) (f (n + 1))) ∧
    ((∀ v : V, ∃ P : List E, G.IsDipath r P v) →
      ∀ s : FordState V E, G.FordReachable c r s → (∀ e : E, ¬ G.IsIncorrect c s.y e) →
        ∃ y : V → ℝ, G.IsFeasiblePotential c r y ∧ (∀ v : V, s.y v = ((y v : ℝ) : WithTop ℝ)) ∧
          ∀ v : V, ∃ P : List E, G.PredDefinesDipath s.p r v P ∧
            G.IsLeastCostDipath c r v P ∧ pathCost c P = y v) := by sorry

end CombOpt.ShortestPath
