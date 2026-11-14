-- Prove2me | Theorems.Thm_APFPaper5_K1_size_pooled
-- name    : APFPaper5.K1.size_pooled
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:46:04.560611+00:00
-- url     : https://prove2.me/theorems/f5cc332a-0e23-49ba-8449-314fb3a0eb73
-- title:
--   The length of pooled run lists is the sum of their lengths
-- statement:
--   For any two finite lists A and B of runs, the length of A followed by B equals length(A)+length(B). This is a list-concatenation identity. It makes no assertion about distinct outcomes, stable frequencies, independence of runs or a physical mixing process.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_pooled_counts.lean:23; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-362;3038-3041

set_option autoImplicit false

universe u

theorem APFPaper5.K1.size_pooled {Run : Type u} (A B : List Run) : (A ++ B).length = A.length + B.length := by sorry
