-- Prove2me | Theorems.Thm_CLRS_DFS_pure_execution_certificate
-- name    : CLRS.DFS.pure_execution_certificate
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T03:55:57.774065+00:00
-- url     : https://prove2.me/theorems/7fe19241-d5a3-4454-acff-17522f57b40e
-- title:
--   Ordered recursive DFS: finite execution and local invariants
-- statement:
--   Let $G$ be a finite directed multigraph with $n$ vertices and $m$ stored adjacency occurrences, including duplicates and self-loops. Let $q$ be any permutation of its vertices, represented by the supplied sequence prefix. Starting from white colors, zero timestamps and counters, and $-1$ parent, finish-order and label entries, the ordinary ordered recursive DFS has a finite big-step execution ending in a state $s$, with traversal event count $k$, such that
--
--   $$
--   \operatorname{clock}(s)=2n,\qquad \operatorname{finished}(s)=n,\qquad k\le 6n+2m.
--   $$
--
--   Every vertex is black. There are $c\le n$ predecessor trees, numbered from zero. The output satisfies the local DFS certificate: positive distinct discovery and finish times within $1,\ldots,2n$; no coinciding discovery/finish events; disjoint or nested vertex intervals; a nonroot parent is an adjacent vertex whose interval is the nearest strict enclosing interval; every edge target is discovered before its source finishes; roots respect their input priority; the finish-order prefix is a permutation strictly increasing in finish time; labels lie in $[0,c)$ and cover that range, are inherited by children, and order roots by discovery time.
--
--   The cost includes all vertex visits, all adjacency occurrences and all outer-loop iterations. The implementation's four fixed entry, constructor, initial-loop and return events are excluded. This is the purely mathematical execution lemma used by the concrete heap-level DFS proof; it also supplies the shared DFS prerequisite for Kosaraju's algorithm.
-- source:
--   CLRS, Introduction to Algorithms, fourth edition, Section 20.3, DFS and DFS-VISIT, Theorems 20.7 and 20.9. Pure big-step transcription of the existing generated program in Definitions.Def_CLRS_DFS_Program on Prove2Me. Supporting source: Jessica Su, Stanford CS 161 Lecture 10, Sections 2.1–2.4, PDF pages 4–9, https://web.stanford.edu/class/archive/cs/cs161/cs161.1168/lecture10-draft.pdf .

import Definitions.Def_CLRS_DFS_PureExecution

set_option autoImplicit false
open Algo2LeanGenerated CLRS.GraphTraversal CLRS.DFS CLRS.DFS.Pure

theorem CLRS.DFS.pure_execution_certificate (g : Graph) (input : Seq) (values : List Int)
    (permutation : values.Perm ((List.range g.size).map Int.ofNat))
    (observed : ∀ i : Nat, i < g.size → input i = values[i]!) :
    ∃ (a : Pure.State) (k : Nat),
      Eval g (.roots values) initial a k ∧ Completed g input a ∧
      k ≤ 6 * g.size + 2 * edgeCount g := by sorry
