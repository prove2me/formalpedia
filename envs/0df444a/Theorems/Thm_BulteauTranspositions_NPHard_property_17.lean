-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_property_17
-- name    : BulteauTranspositions.NPHard.property_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:54:00.761571+00:00
-- url     : https://prove2.me/theorems/b2832986-c99e-44b9-933d-d77db54ed7a7
-- title:
--   Property 17 — var block activation orders
-- statement:
--   For a variable block [A₁,A₂]=var(A) in a valid context, the complete possible local activation orders are exactly (A₁,A,A₂), (A₂,A,A₁), (A,A₁,A₂) and (A,A₂,A₁). Each listed order is realizable in the local behavior graph, and no other complete order is realizable.
--
--   Differences from the source:
--   - reading: possible orders in a block in a valid context → complete port-label paths in the operational local behavior graph; reason: pp.14–16 define local arcs and study each block independently; this includes realizability and does not require any fixed surrounding network to supply all inputs
--   - encoding: arbitrary fresh internal symbols and three distinct port variables → canonical disjoint even port labels and odd internal labels, with all three wire identifiers distinct; reason: every basic block admits this injective relabeling; activation paths are invariant under renaming
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Property 17, printed p. 21 = PDF p. 21; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Blocks

namespace BulteauTranspositions.NPHard

theorem property_17 (w0 w1 w2 h : ℕ) (hw : [w0,w1,w2].Nodup)
    (order : List Variable) :
    ActivationOrder ⟨.var,w0,w1,w2⟩ h order ↔
      order = [wire w1,wire w0,wire w2] ∨
      order = [wire w2,wire w0,wire w1] ∨
      order = [wire w0,wire w1,wire w2] ∨
      order = [wire w0,wire w2,wire w1] := by sorry

end BulteauTranspositions.NPHard
