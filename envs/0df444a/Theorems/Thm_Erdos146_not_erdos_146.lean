-- Prove2me | Theorems.Thm_Erdos146_not_erdos_146
-- name    : Erdos146.not_erdos_146
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:54:55.6014+00:00
-- url     : https://prove2.me/theorems/672dd2e7-0377-418e-be96-1ab98da4c1e6
-- title:
--   Erdős problem #146 is false
-- statement:
--   Erdős problem #146 asks whether every fixed bipartite $r$-degenerate graph $H$ satisfies $\mathrm{ex}(n,H) = O(n^{2-1/r})$. This is the negation: the statement is **false**, by the $r = 2$ counterexample of Theorem 1.2.
--
--   A graph $H$ is **$r$-degenerate** if every nonempty subgraph of $H$ has a vertex of degree at most $r$. Erdős conjectured (Erdős problem #146) that every fixed bipartite $r$-degenerate graph $H$ satisfies $\mathrm{ex}(n,H) = O(n^{2-1/r})$. Chapter 10 of the source disproves this for $r = 2$.
--
--   The source also notes a consequence for a related conjecture of Erdős (problem #113), which asserts that a bipartite graph $H$ is 2-degenerate if and only if $\mathrm{ex}(n,H) = O(n^{3/2})$. Janzer had already disproved the reverse implication; Theorem 1.2 refutes the forward one.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L18543-L18584

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.not_erdos_146 :
    ¬ DegeneracyConjectureStatement := by sorry
