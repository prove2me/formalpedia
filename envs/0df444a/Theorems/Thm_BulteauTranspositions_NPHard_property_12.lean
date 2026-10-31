-- Prove2me | Theorems.Thm_BulteauTranspositions_NPHard_property_12
-- name    : BulteauTranspositions.NPHard.property_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T21:54:19.397319+00:00
-- url     : https://prove2.me/theorems/256953e4-d5c0-4d47-a728-72815ca4c02c
-- title:
--   Property 12 — internal-step and activation effects on blocks
-- statement:
--   Suppose the external triples of a block-decomposed instance (I,B) are partitioned into valid variables A, and a well-ordered triple t=(d,e,f) yields (I′,B′). One of two cases holds. If t is internal in block h₀, every surviving symbol stays in its block, and the order of any two surviving symbols in the same block other than h₀ is preserved. Otherwise t is the activation triple (x,y,z) of a variable [(a,b,c),(x,y,z)] in A; b moves to that variable’s target block, every other surviving symbol stays in its block, and the order of every pair of surviving symbols other than b is preserved.
--
--   Differences from the source:
--   - encoding: finite alphabets and a set of disjoint oriented triples → natural-number symbol names and a list of triples with a duplicate-free flattened alphabet; reason: finite alphabets admit injective naming; triple list order has no operational significance
--   - encoding: a set partition of external triples and an l-block decomposition → lists with exact membership and no duplicates, and cuts whose final endpoint is the span; reason: list order is auxiliary; block numbering and occupied-symbol order agree with the source
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, Property 12, printed p. 12 = PDF p. 12; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Blocks

namespace BulteauTranspositions.NPHard

theorem property_12 (C D : Context) (As : List Variable) (t : Triple)
    (hpart : VariablePartition C As) (hvalid : ∀ A ∈ As, A.Valid C)
    (hs : ContextStep C t D) :
    (Internal C t ∧
      (∀ a ∈ D.inst.symbols, D.block a = C.block a) ∧
      ∀ a ∈ D.inst.symbols, ∀ b ∈ D.inst.symbols,
        D.block a = D.block b → D.block a ≠ C.block t.1 →
        C.inst.Before a b → D.inst.Before a b) ∨
    (∃ A ∈ As, t = A.xyz ∧ D.block A.abc.2.1 = C.block A.abc.1 ∧
      (∀ a ∈ D.inst.symbols, a ≠ A.abc.2.1 → D.block a = C.block a) ∧
      ∀ a ∈ D.inst.symbols, ∀ b ∈ D.inst.symbols,
        a ≠ A.abc.2.1 → b ≠ A.abc.2.1 → C.inst.Before a b → D.inst.Before a b) := by sorry

end BulteauTranspositions.NPHard
