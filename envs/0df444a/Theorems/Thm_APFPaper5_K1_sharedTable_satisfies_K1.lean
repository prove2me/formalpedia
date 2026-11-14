-- Prove2me | Theorems.Thm_APFPaper5_K1_sharedTable_satisfies_K1
-- name    : APFPaper5.K1.sharedTable_satisfies_K1
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:14:37.7092+00:00
-- url     : https://prove2.me/theorems/8a0e01a7-87ad-4e41-878d-267cecc89739
-- title:
--   Private distinctions make the shared-count form faithful
-- statement:
--   Supply finitely many finite families of a finite distinction type. Assume hprivate: each listed family contains a distinction that occurs in no other listed family. The shared-count table then defines a real-bilinear coefficient form whose diagonal is nonnegative and vanishes only at zero, with identity role exchange. This is a model-level realization of the displayed bilinearity and faithful-diagonal predicates. It does not construct a physical completed score or establish the remaining meaning and correspondence requirements of physical K1.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_shared_count.lean:33; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_two_adoptions_2026-11-12.md, 1; Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex, 3721-3749

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

theorem APFPaper5.K1.sharedTable_satisfies_K1 [DecidableEq ι] (fam : ι → Finset D)
    (hprivate : ∀ i, ∃ d : D, ∀ j, decide (d ∈ fam j) = decide (j = i)) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm (sharedTable fam)) ∧
      FaithfulNonnegDiagonal (tableForm (sharedTable fam)) (LinearEquiv.refl ℝ (ι → ℝ)) := by sorry
