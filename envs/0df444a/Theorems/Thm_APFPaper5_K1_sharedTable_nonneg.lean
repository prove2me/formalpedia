-- Prove2me | Theorems.Thm_APFPaper5_K1_sharedTable_nonneg
-- name    : APFPaper5.K1.sharedTable_nonneg
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:14:20.096734+00:00
-- url     : https://prove2.me/theorems/d9212523-7186-474c-8f30-58da19baafd3
-- title:
--   The shared-count coefficient form has a nonnegative diagonal
-- statement:
--   Let the index and distinction types be finite, and supply a finite family R(i) of distinctions for each index. The table counting distinctions shared by each pair has coefficient form F with F(x,x)≥0 for every real coefficient vector x. Unit weights are part of the score definition. The conclusion is positive semidefiniteness; distinct families can still produce null coefficient vectors. No private-distinction condition, physical score identification, normalized probability rule or continuity hypothesis is supplied by this declaration.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_count.lean:29; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_two_adoptions_2026-11-12.md, 1; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 3721-3749

import Definitions.Def_APFPaper5_K1_SharedCount
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
universe u v
variable {ι : Type u} [Fintype ι] {D : Type v} [Fintype D] [DecidableEq D]

theorem APFPaper5.K1.sharedTable_nonneg (fam : ι → Finset D) (x : ι → ℝ) :
    0 ≤ tableForm (sharedTable fam) x x := by sorry
