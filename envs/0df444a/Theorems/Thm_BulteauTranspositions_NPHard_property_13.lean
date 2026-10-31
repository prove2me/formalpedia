-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_property_13
-- name    : BulteauTranspositions.NPHard.property_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:53:54.415993+00:00
-- url     : https://prove2.me/theorems/6d36b14a-cbaa-4cf3-bd2e-bd56b73eec56
-- title:
--   Property 13 — external triples remain paired into variables
-- statement:
--   After any one 3DT-step from a valid context, the new external triples can be partitioned into variables satisfying conditions (i) and (ii) of Definition 12: the prescribed source and target placements in distinct blocks. The conclusion does not assert the two order conditions (iii) and (iv).
--
--   Differences from the source:
--   - encoding: finite alphabets and a set of disjoint oriented triples → natural-number symbol names and a list of triples with a duplicate-free flattened alphabet; reason: finite alphabets admit injective naming; triple list order has no operational significance
--   - encoding: a set partition of external triples and an l-block decomposition → lists with exact membership and no duplicates, and cuts whose final endpoint is the span; reason: list order is auxiliary; block numbering and occupied-symbol order agree with the source
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Property 13, printed p. 14 = PDF p. 14; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Blocks

namespace BulteauTranspositions.NPHard

theorem property_13 (C D : Context) (t : Triple) (hv : ValidContext C)
    (hs : ContextStep C t D) :
    ∃ As, VariablePartition D As ∧ ∀ A ∈ As, A.Located D := by sorry

end BulteauTranspositions.NPHard
