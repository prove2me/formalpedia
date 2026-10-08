-- Prove2me | Theorems.Thm_ChinesePostman_NextNode_theorem_5_2
-- name    : ChinesePostman.NextNode.theorem_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:51:28.080088+00:00
-- url     : https://prove2.me/theorems/aca92413-a31b-4ab0-a1bc-a5d24f2603a2
-- title:
--   Theorem 5.2, p. 112 — the next-node algorithm's lists satisfy Theorem 5.1 (i), (ii) and (iii)
-- statement:
--   Let $G$ be an even, connected, finite loopless multigraph, $r$ a node and $e_0$ an edge meeting $r$. Run the next-node algorithm of §5.2 from $r$, starting with the edge $e_0$:
--
--   - **Step 0.** $n_0 = n = r$, $e = e_0$, all lists empty, all edges unused.
--   - **Step 1.** Let $m$ be the node other than $n$ meeting $e$; append $n$ to the end of $L_m$; $e$ is now used. If $m$ meets an unused edge, go to Step 2; otherwise go to Step 3.
--   - **Step 2.** Change $n$ to $m$ and let $e$ be any unused edge meeting $m$; go to Step 1.
--   - **Step 3.** Let $n_0$ be any node meeting a used edge and an unused edge $e$; change $n$ to $n_0$ and go to Step 1. If no such $n_0$ exists, terminate.
--
--   Then for every choice made along the way, the lists $L$ at termination satisfy
--
--   $$
--   \text{(i)}\ \ 2k_n = \deg(n)\ \forall n, \qquad \text{(ii)}\ \ \#(n,m) = |\{i: L_m(i) = n\}| + |\{i : L_n(i) = m\}|\ \forall n,m, \qquad \text{(iii)}\ \ n \mapsto L_n(1),\ n \ne r, \text{ is an arborescence with root } r .
--   $$
--
--   Combined with Theorem 5.1, the lists produced by the algorithm describe an Euler tour.
--
--   **Formalization Note** Step 0 needs an edge meeting $r$, which is the added hypothesis $r \in e_0$; for a graph with no edges the algorithm cannot start and the statement is vacuous. "Produced by the algorithm" means: a terminated state is reachable from the Step 0 state by the steps above, each nondeterministic choice ("any unused edge", "any node $n_0$") being a branch. Condition (iii) is stated for $L_n(1)$, as in Theorem 5.1 and in the paper's proof of Theorem 5.2.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 112, Theorem 5.2, with the next-node algorithm of §5.2, p. 111

import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Theorem 5.2, p. 112: the next-node lists created by any complete run of the next-node algorithm
(§5.2, p. 111) on an even, connected graph, started at `r` with an edge `e₀` meeting `r`, satisfy
Theorem 5.1 (i), (ii) and (iii). -/
theorem theorem_5_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hconn : Connected G) (heven : ∀ n, Even (degree G n)) (r : V) (e₀ : E)
    (hr : r ∈ G.ends e₀) (L : V → List V) (hL : AlgProduces G r e₀ L) :
    CondI G L ∧ CondII G L ∧ CondIII G r L := by sorry

end ChinesePostman.NextNode
