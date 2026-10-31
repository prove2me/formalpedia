-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_property_15
-- name    : BulteauTranspositions.NPHard.property_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:53:49.359145+00:00
-- url     : https://prove2.me/theorems/8131d1ab-976b-4fe6-9ae5-9016afe6d169
-- title:
--   Property 15 — and block activation orders
-- statement:
--   For a conjunction block A=and(A₁,A₂) in a valid context, the complete possible local activation orders are exactly (A₁,A₂,A) and (A₂,A₁,A). Each listed order is realizable in the local behavior graph, and no other complete order is realizable.
--
--   Differences from the source:
--   - reading: possible orders in a block in a valid context → complete port-label paths in the operational local behavior graph; reason: pp.14–16 define local arcs and study each block independently; this includes realizability and does not require any fixed surrounding network to supply all inputs
--   - encoding: arbitrary fresh internal symbols and three distinct port variables → canonical disjoint even port labels and odd internal labels, with all three wire identifiers distinct; reason: every basic block admits this injective relabeling; activation paths are invariant under renaming
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Property 15, printed p. 17 = PDF p. 17; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Blocks

namespace BulteauTranspositions.NPHard

theorem property_15 (w0 w1 w2 h : ℕ) (hw : [w0,w1,w2].Nodup)
    (order : List Variable) :
    ActivationOrder ⟨.and,w0,w1,w2⟩ h order ↔
      order = [wire w1,wire w2,wire w0] ∨
      order = [wire w2,wire w1,wire w0] := by sorry

end BulteauTranspositions.NPHard
