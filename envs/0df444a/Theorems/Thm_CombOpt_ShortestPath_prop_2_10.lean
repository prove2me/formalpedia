-- Prove2me | Theorems.Thm_CombOpt_ShortestPath_prop_2_10
-- name    : CombOpt.ShortestPath.prop_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:06:00.215318+00:00
-- url     : https://prove2.me/theorems/a5b829c2-ef38-4211-83d1-51c951f07b24
-- title:
--   Proposition 2.10 — invariants of Ford's Algorithm without negative-cost dicircuits
-- statement:
--   Let $G$ be a finite digraph with real arc costs $c$ and root $r$, and suppose $(G,c)$ has **no negative-cost dicircuit**. Consider any stage of any execution of Ford's Algorithm, that is, any state $(y,p)$ obtained from the initialization ($y_r=0$, $p(r)=0$, $y_v=\infty$, $p(v)=-1$ for $v\ne r$) by finitely many corrections of incorrect arcs, chosen in any order. Then for every node $v$:
--
--   1. if $y_v\ne\infty$, then $y_v$ is the cost of a simple dipath from $r$ to $v$;
--   2. if $p(v)\ne-1$, then $p$ defines a simple dipath $P$ from $r$ to $v$ with $c(P)\le y_v$.
--
--   This is the main step in the proof that Ford's Algorithm terminates with least-cost dipaths (Theorem 2.11): there are only finitely many simple dipaths, hence finitely many possible label values.
--
--   Differences from the source:
--   - generalization: the section may assume G simple (p. 20) and p(w) stores the node v → loops and parallel arcs allowed, p(w) stores the corrected arc vw; reason: on a simple digraph the arc vw and its tail v determine each other, so the Lean statement specializes to the book's
--   - generalization: the section assumes that dipaths exist from r to all the nodes (p. 20) → no reachability hypothesis; reason: nodes unreachable from r keep y_v = ∞ and p(v) = −1, so the invariants need no such assumption and the stronger statement implies the book's
--   - encoding: labels in ℝ ∪ {∞}, predecessor values 0 and −1 → WithTop ℝ with ⊤ = ∞, FordPred.root and FordPred.undef; reason: WithTop ℝ obeys the book's rules a + ∞ = ∞ and a < ∞
--   - encoding: "at any stage of the execution" → any state reachable from fordInit r by FordStep (correcting any incorrect arc); reason: the algorithm chooses the incorrect arc freely, so the stages of all executions are exactly these states
--   - encoding: a dipath is the sequence v_0, e_1, v_1, …, e_k, v_k → a start node and the arc list [e_1, …, e_k]; reason: the nodes are the start node and the heads of the arcs
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 2.10, p. 24 (PDF p. 33); algorithm p. 22 (PDF p. 31)

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph_HasNegativeDicircuit
import Definitions.Def_CombOpt_ShortestPath_Digraph_FordReachable
import Definitions.Def_CombOpt_ShortestPath_Digraph_IsSimpleDipath
import Definitions.Def_CombOpt_ShortestPath_Digraph_PredDefinesDipath
import Definitions.Def_CombOpt_ShortestPath_pathCost

namespace CombOpt.ShortestPath

/-- **Proposition 2.10 (invariants of Ford's Algorithm).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Proposition 2.10, p. 24 (PDF p. 33): "If (G, c) has no negative-cost dicircuit, then at
any stage of the execution of Ford's Algorithm we have:
(i) If y_v ≠ ∞, then it is the cost of a simple dipath from r to v;
(ii) If p(v) ≠ −1, then p defines a simple dipath from r to v of cost at most y_v."

Let `G` be a finite digraph with real arc costs `c` and no negative-cost dicircuit, and let
`s` be any state reached from `fordInit r` by finitely many corrections of incorrect arcs (in
any order). Then
(i) for every node `v` with `s.y v ≠ ⊤` there is a simple dipath `P` from `r` to `v` with
`s.y v = c(P)`;
(ii) for every node `v` with `s.p v ≠ undef` there is a simple dipath `P` from `r` to `v`
defined by `s.p` with `c(P) ≤ s.y v`.

**Formalization Note.** `⊤ : WithTop ℝ` is the book's `∞`; `FordPred.undef` is the book's
`−1`; `p` records arcs rather than nodes (see `FordPred`), so parallel arcs and loops are
allowed. -/
theorem prop_2_10 {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : Digraph V E)
    (c : E → ℝ) (r : V) (hc : ¬ G.HasNegativeDicircuit c) (s : FordState V E)
    (hs : G.FordReachable c r s) :
    (∀ v : V, s.y v ≠ ⊤ →
        ∃ P : List E, G.IsSimpleDipath r P v ∧ s.y v = ((pathCost c P : ℝ) : WithTop ℝ)) ∧
    (∀ v : V, s.p v ≠ FordPred.undef →
        ∃ P : List E, G.IsSimpleDipath r P v ∧ G.PredDefinesDipath s.p r v P ∧
          ((pathCost c P : ℝ) : WithTop ℝ) ≤ s.y v) := by sorry

end CombOpt.ShortestPath
