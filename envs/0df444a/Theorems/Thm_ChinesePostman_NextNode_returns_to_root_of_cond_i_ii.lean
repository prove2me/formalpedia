-- Prove2me | Theorems.Thm_ChinesePostman_NextNode_returns_to_root_of_cond_i_ii
-- name    : ChinesePostman.NextNode.returns_to_root_of_cond_i_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:51:16.30305+00:00
-- url     : https://prove2.me/theorems/c7eba1de-1740-4b5d-8ebb-cf95c5362938
-- title:
--   Proof of Theorem 5.1, p. 113 — under (i) and (ii) the tour from $r$ returns to $r$ having traversed every edge meeting $r$
-- statement:
--   Let $G$ be a finite loopless multigraph, $r$ a node and $L$ next-node lists satisfying (i) $2k_n = \deg(n)$ for every $n$ and (ii) $\#(n,m) = |\{i : L_m(i) = n\}| + |\{i : L_n(i) = m\}|$ for all $n, m$. Follow the tour specified by the lists from $r$ until it stops. Then
--
--   1. the traversal ends at $r$;
--   2. every entry of the list of $r$ has been used: $r$ has been left $k_r$ times;
--   3. every occurrence of $r$ in every list $L_m$ has been used,
--
--   so every edge meeting $r$ has been traversed.
--
--   This is the first step of the converse of Theorem 5.1: the specified tour cannot get stuck at a node other than $r$.
--
--   **Formalization Note** "An entry has been used" refers to the traversal's departure counters: with $t_m$ departures made from $m$, the unused entries of $L_m$ are $L_m(1), \dots, L_m(k_m - t_m)$. Condition (iii) and connectivity are not needed. Even degrees follow from (i) and are not assumed separately.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 113, §5, proof of Theorem 5.1 (converse, first step)

import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Proof of Theorem 5.1, p. 113 (converse, first step): under (i) and (ii), the traversal from `r`
specified by the next-node lists ends at `r`, having used every entry of `L r` and every occurrence
of `r` in every list (so every edge meeting `r` has been traversed). -/
theorem returns_to_root_of_cond_i_ii {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Graph V E) (r : V) (L : V → List V) (h1 : CondI G L) (h2 : CondII G L) :
    (follow L r).1.getLast? = some r ∧ (follow L r).2 r = (L r).length ∧
      ∀ m, r ∉ unused L (follow L r).2 m := by sorry

end ChinesePostman.NextNode
