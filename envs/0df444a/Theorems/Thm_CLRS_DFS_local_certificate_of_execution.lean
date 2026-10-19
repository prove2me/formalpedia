-- Prove2me | Theorems.Thm_CLRS_DFS_local_certificate_of_execution
-- name    : CLRS.DFS.local_certificate_of_execution
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T04:04:27.535929+00:00
-- url     : https://prove2.me/theorems/c7a190e9-ee72-4350-b880-5f40fba6dd4a
-- title:
--   Finite ordered DFS executions satisfy the local forest invariants
-- statement:
--   Let $G$ be a finite directed multigraph with $n$ vertices, allowing parallel adjacency occurrences and self-loops. Let $q$ be a permutation of its vertices, and suppose the supplied sequence agrees with $q$ on its first $n$ entries. Start recursive ordered DFS with white colors, zero timestamps and counters, and $-1$ parent, finish-order and tree-label entries.
--
--   For every finite execution of the complete outer loop ending in state $s$, the parent array $p$, discovery times $d$, finish times $f$, finish-order sequence $o$, and tree labels $b$ satisfy
--
--   $$
--   \operatorname{LocalCertificate}(G,q,p,d,f,o,b,c),\qquad
--   c=\max\{\operatorname{count}(s),0\}.
--   $$
--
--   The certificate asserts positive distinct timestamps within $1,\ldots,2n$, distinct discovery and finish events, and disjoint or nested vertex intervals. A nonroot parent is adjacent to its child and is the nearest strict enclosing interval. Every edge target is discovered before its source finishes. Root discoveries respect the supplied input priority, and the finish-order prefix is a vertex permutation in strictly increasing finish time.
--
--   Labels lie in $[0,c)$, every label occurs, parent links preserve labels, and labels order roots in discovery order. This is the invariant-preservation part of DFS correctness. It assumes a finite execution and makes no assertion that such an execution exists or that it meets an event budget; termination and accounting can be established independently.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition, Section 20.3, DFS and DFS-VISIT, Theorems 20.7 and 20.9. Pure execution relation in Definitions.Def_CLRS_DFS_PureExecution. Supporting proof reference: Jessica Su, Stanford CS161 Lecture 10, Sections 2.1 and 2.3–2.4, PDF pages 4–9, https://web.stanford.edu/class/archive/cs/cs161/cs161.1168/lecture10-draft.pdf .

import Definitions.Def_CLRS_DFS_PureExecution

set_option autoImplicit false
open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS CLRS.DFS.Pure

theorem CLRS.DFS.local_certificate_of_execution (g : Graph) (input : Seq) (values : List Int)
    (permutation : values.Perm ((List.range g.size).map Int.ofNat))
    (observed : ∀ i : Nat, i < g.size → input i = values[i]!)
    (a : Pure.State) (k : Nat) (execution : Eval g (.roots values) initial a k) :
    LocalCertificate g input (a.arrays 1) (a.arrays 2) (a.arrays 3)
      (a.arrays 4) (a.arrays 5) a.count.toNat := by sorry
