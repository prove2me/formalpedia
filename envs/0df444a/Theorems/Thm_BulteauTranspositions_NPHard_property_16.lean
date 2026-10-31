-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_property_16
-- name    : BulteauTranspositions.NPHard.property_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:53:58.354987+00:00
-- url     : https://prove2.me/theorems/d7a4f8cd-2eb7-4e4d-8940-e2c61fe11247
-- title:
--   Property 16 — or block activation orders
-- statement:
--   For a disjunction block A=or(A₁,A₂) in a valid context, the complete possible local activation orders are exactly (A₁,A,A₂), (A₂,A,A₁), (A₁,A₂,A) and (A₂,A₁,A). Each listed order is realizable in the local behavior graph, and no other complete order is realizable.
--
--   Differences from the source:
--   - reading: possible orders in a block in a valid context → complete port-label paths in the operational local behavior graph; reason: pp.14–16 define local arcs and study each block independently; this includes realizability and does not require any fixed surrounding network to supply all inputs
--   - encoding: arbitrary fresh internal symbols and three distinct port variables → canonical disjoint even port labels and odd internal labels, with all three wire identifiers distinct; reason: every basic block admits this injective relabeling; activation paths are invariant under renaming
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Property 16, printed p. 17 = PDF p. 17; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Blocks

namespace BulteauTranspositions.NPHard

theorem property_16 (w0 w1 w2 h : ℕ) (hw : [w0,w1,w2].Nodup)
    (order : List Variable) :
    ActivationOrder ⟨.or,w0,w1,w2⟩ h order ↔
      order = [wire w1,wire w0,wire w2] ∨
      order = [wire w2,wire w0,wire w1] ∨
      order = [wire w1,wire w2,wire w0] ∨
      order = [wire w2,wire w1,wire w0] := by sorry

end BulteauTranspositions.NPHard
