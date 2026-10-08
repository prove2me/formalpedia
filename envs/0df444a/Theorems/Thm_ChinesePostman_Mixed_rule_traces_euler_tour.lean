-- Prove2me | Theorems.Thm_ChinesePostman_Mixed_rule_traces_euler_tour
-- name    : ChinesePostman.Mixed.rule_traces_euler_tour
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:51:59.383905+00:00
-- url     : https://prove2.me/theorems/81fb6a5b-ae4f-4e07-8a6e-c7206fc5980f
-- title:
--   §6, pp. 116–117 — the Rule traces an Euler tour when the arborescence edge is last at every node
-- statement:
--   Let $G$ be a mixed graph in which
--
--   1. the directed edges form a symmetric, connected spanning subgraph of $G$;
--   2. the undirected edges form an even-degree subgraph: every node meets an even number of undirected edges.
--
--   Let $a_n$ ($n \neq r$) be the edges of a spanning arborescence of directed edges with root $r$. At each node $n$ let $U_n$ be an ordering of the undirected edges meeting $n$, in any order, and $D_n$ an ordering of the directed edges away from $n$ in which, for $n \neq r$, the arborescence edge $a_n$ is last (the order at $r$ is arbitrary). Start at $r$ and follow the **Rule**: whenever node $n$ is reached, leave $n$ by the next unused undirected edge in $U_n$ if one is available; if all undirected edges at $n$ have been used, leave by the next unused edge of $D_n$. Then the resulting traversal
--
--   $$
--   (r = n_1, e_1, n_2, \dots, e_{|E|}, n_{|E|+1} = r)
--   $$
--
--   is an Euler tour of the mixed graph: it returns to $r$, uses every edge exactly once, and traverses every directed edge in its direction.
--
--   This is the paper's algorithm for specifying an Euler tour; it extends the van Aardenne-Ehrenfest–de Bruijn construction for symmetric directed graphs.
--
--   **Formalization Note** "Unused" is global: an undirected edge used when leaving its other end is no longer available. The traversal is computed for at most $|E|$ steps and stops early if the Rule finds no unused edge at the current node; the conclusion asserts that the computed node and edge sequences form a mixed Euler tour starting at $r$.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), pp. 116–117, §6 (orderings of undirected and directed edges, the Rule, 'We now prove that this rule will produce an Euler tour')

import Mathlib
import Definitions.Def_ChinesePostman_Mixed_Setting

namespace ChinesePostman.Mixed

/-- §6, pp. 116–117, the Rule: let the directed edges of a mixed graph form a symmetric, connected
spanning subgraph and the undirected edges an even-degree subgraph. Given a spanning arborescence
of directed edges with root `r`, an ordering `U n` of the undirected edges meeting each node `n`
and an ordering `D n` of the directed edges away from `n` in which the arborescence edge `a n` is
last for `n ≠ r`, the traversal from `r` by the Rule (leave by the next unused undirected edge if
one is available, otherwise by the next unused edge directed away from the node) is an Euler tour
of the mixed graph. -/
theorem rule_traces_euler_tour {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : MixedGraph V E) (hsym : G.IsSymmetric) (hconn : G.DirectedConnected)
    (heven : ∀ n, Even (G.undirDeg n))
    (r : V) (a : V → Option E) (harb : G.IsArborescence Finset.univ r a)
    (U D : V → List E)
    (hU : ∀ n, (U n).Nodup ∧
      ∀ e, e ∈ U n ↔ (G.directed e = false ∧ (G.tail e = n ∨ G.head e = n)))
    (hD : ∀ n, (D n).Nodup ∧ ∀ e, e ∈ D n ↔ (G.directed e = true ∧ G.tail e = n))
    (hlast : ∀ n, n ≠ r → (D n).getLast? = a n) :
    G.IsMixedEulerTour (ruleRun G U D (Fintype.card E) r []).1
      (ruleRun G U D (Fintype.card E) r []).2 ∧
    (ruleRun G U D (Fintype.card E) r []).1.head? = some r := by sorry

end ChinesePostman.Mixed
