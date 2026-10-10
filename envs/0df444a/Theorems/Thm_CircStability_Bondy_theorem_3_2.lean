-- Prove2me | Theorems.Thm_CircStability_Bondy_theorem_3_2
-- name    : CircStability.Bondy.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:43:09.577998+00:00
-- url     : https://prove2.me/theorems/1a84c77b-43f8-4d02-9dfc-e1cbfbfff744
-- title:
--   Theorem 3.2 — many edges off a longest cycle of length 4 ≤ c < n force c ∈ {6,7,9}, a vertex with ⌊c/2⌋ neighbours on C, or a long cycle nearly disjoint from C
-- statement:
--   Let $G$ be a graph on $n$ vertices (no connectivity is assumed) and let $C$ be a longest cycle of $G$ of length $c$, where $4 \le c \le n-1$. If
--
--   $$e(G-C) + e(G-C, C) > \left(\left\lfloor \tfrac c2 \right\rfloor - 1\right)(n-c),$$
--
--   then one of the following holds:
--
--   1. $c \in \{6,7,9\}$;
--   2. there is a vertex $u \notin V(C)$ with exactly $\lfloor c/2\rfloor$ neighbours on $C$;
--   3. there is a cycle $C'$ of $G$ with $|V(C)\cap V(C')| \le 1$ such that $|C'| \ge 2\lfloor c/2\rfloor - 3$ if $V(C) \cap V(C') = \emptyset$, and $|C'| \ge 2\lfloor c/2\rfloor - 1$ if $|V(C)\cap V(C')| = 1$.
--
--   This is the connectivity-free form of the step that finds a vertex with many neighbours on a longest cycle.
--
--   **Formalization Note** $e(G-C)+e(G-C,C)$ is the number of edges with at most one endpoint in $V(C)$; $|C'|$ is the number of edges of $C'$. With $c \ge 4$ the natural-number subtractions $2\lfloor c/2\rfloor - 3$ and $\lfloor c/2 \rfloor - 1$ are exact.
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 11, Theorem 3.2

import Mathlib
import Definitions.Def_CircStability_Bondy_Setting
open SimpleGraph Finset

namespace CircStability.Bondy
theorem theorem_3_2 (n c : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u : Fin n} (C : G.Walk u u) (hC : IsLongestCycle G C) (hlen : C.length = c)
    (hc : 4 ≤ c) (hcn : c < n)
    (hE : (c / 2 - 1) * (n - c) < edgesOffCycle G (cycleVerts C)) :
    (c = 6 ∨ c = 7 ∨ c = 9) ∨
      (∃ v, v ∉ cycleVerts C ∧ #(G.neighborFinset v ∩ cycleVerts C) = c / 2) ∨
      (∃ (w : Fin n) (D : G.Walk w w), D.IsCycle ∧
        #(cycleVerts C ∩ D.support.toFinset) ≤ 1 ∧
        (#(cycleVerts C ∩ D.support.toFinset) = 0 → 2 * (c / 2) - 3 ≤ D.length) ∧
        (#(cycleVerts C ∩ D.support.toFinset) = 1 → 2 * (c / 2) - 1 ≤ D.length)) := by sorry
end CircStability.Bondy
