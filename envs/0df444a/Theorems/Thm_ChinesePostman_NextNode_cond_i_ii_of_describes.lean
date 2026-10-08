-- Prove2me | Theorems.Thm_ChinesePostman_NextNode_cond_i_ii_of_describes
-- name    : ChinesePostman.NextNode.cond_i_ii_of_describes
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:50:52.925335+00:00
-- url     : https://prove2.me/theorems/ca52ff11-69e7-463b-ad9f-19504acb6a60
-- title:
--   Proof of Theorem 5.1, pp. 112–113 — lists describing an Euler tour satisfy (i) and (ii)
-- statement:
--   Let $G$ be a finite loopless multigraph, $r$ a node and $L_n(1), \dots, L_n(k_n)$ next-node lists for $G$. If the lists describe an Euler tour from $r$ (the traversal from $r$ uses every list entry and its node sequence is that of an Euler tour), then
--
--   $$
--   \text{(i)}\quad k_n = \tfrac12 \deg(n) \ \text{ for every node } n, \qquad \text{(ii)}\quad \#(n,m) = \bigl|\{i : L_m(i) = n\}\bigr| + \bigl|\{i : L_n(i) = m\}\bigr| \ \text{ for all nodes } n, m,
--   $$
--
--   where $\#(n,m)$ is the number of edges meeting both $n$ and $m$.
--
--   This is the easy half of the necessity part of Theorem 5.1: an Euler tour leaves a node once each time it enters it, and uses each edge once.
--
--   **Formalization Note** Connectivity and even degrees, hypotheses of Theorem 5.1, are not needed here and are omitted. Condition (ii) is stated for all pairs, including $n = m$, where it says that no list contains its own node.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), pp. 112–113, §5, proof of Theorem 5.1 (necessity of (i) and (ii))

import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Proof of Theorem 5.1, pp. 112–113: if next-node lists describe an Euler tour, then they
satisfy (i) and (ii). -/
theorem cond_i_ii_of_describes {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (r : V) (L : V → List V)
    (h : DescribesEulerTour G r L) :
    CondI G L ∧ CondII G L := by sorry

end ChinesePostman.NextNode
