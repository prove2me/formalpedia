-- Prove2me | Theorems.Thm_EdmondsKarp_ShortestPath_chain_simple
-- name    : EdmondsKarp.ShortestPath.chain_simple
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T19:31:16.347526+00:00
-- url     : https://prove2.me/theorems/a565504b-491d-4163-a237-02557452aac6
-- title:
--   Every finite directed walk admits a no-longer simple path
-- statement:
--   Every finite list forming a chain for a binary relation admits a list of distinct vertices forming a chain for the same relation, with identical first and last vertices and no greater length.
-- source:
--   Auxiliary directed-path lemmas for Edmonds and Karp (1972), §1.1 p. 249 and §1.2 pp. 251–252. DOI: 10.1145/321694.321699.

import Mathlib

theorem EdmondsKarp.ShortestPath.chain_simple {V : Type} [DecidableEq V] (R : V → V → Prop) (P : List V)
    (hP : P.IsChain R) :
    ∃ Q : List V, Q.Nodup ∧ Q.IsChain R ∧ Q.head? = P.head? ∧
      Q.getLast? = P.getLast? ∧ Q.length ≤ P.length := by sorry
