-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_exists_lawfulExactOracle
-- name    : ChenCapacityTerminals.Exact.exists_lawfulExactOracle
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:05:22.51411+00:00
-- url     : https://prove2.me/theorems/04bab9e3-28a2-4bf6-af72-d308f1e4b2ef
-- title:
--   Existence of an exact real-capacity flow-and-shore oracle
-- statement:
--   There is a choice function $O$ which, for every valid directed arc-record network with real nonnegative capacities and distinct root and sink, returns an arc-indexed flow of the correct length together with an $r$–$z$ sink side. The flow respects every capacity, conserves at all nonterminal vertices, and its divergence at the source is exactly the entering capacity of the returned shore.
--
--   Invalid queries need no restriction. On valid queries, the required answer is obtained from an ordinary maximum $r$–$z$ flow and its matching minimum shore, with arbitrary ties. Real arc capacities and parallel or looping records are allowed. This is the pure existence statement behind the fixed-pair oracle used in Lemma 3.1; it makes no computational claim.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), Lemma 3.1 proof, p. 6, PDF p. 7 (“A cut … any minimum cut gives the stated minimizer”); ordinary max-flow/min-cut existence for finite directed networks.

import Definitions.Def_ChenCapacityTerminals_Exact_ExactExecution

set_option autoImplicit false

theorem ChenCapacityTerminals.Exact.exists_lawfulExactOracle : ∃ O, LawfulExactOracle O := by sorry
