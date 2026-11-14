-- Prove2me | Theorems.Thm_APFPaper5_K1_passes_pooled
-- name    : APFPaper5.K1.passes_pooled
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:41:27.86537+00:00
-- url     : https://prove2.me/theorems/30be1b83-31ef-4bca-be61-86417a61c0af
-- title:
--   Passing-run counts add when finite run lists are pooled
-- statement:
--   For any run type, Boolean pass predicate and finite lists A and B, the number of passing entries in their concatenation equals the sum of their separate passing counts. Repeated list entries are counted as entries. No frequency limit or physical mixture interpretation is assumed.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_pooled_counts.lean:19; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-362;3038-3041

set_option autoImplicit false

universe u

theorem APFPaper5.K1.passes_pooled {Run : Type u} (passes : Run → Bool) (A B : List Run) :
    (A ++ B).countP passes = A.countP passes + B.countP passes := by sorry
