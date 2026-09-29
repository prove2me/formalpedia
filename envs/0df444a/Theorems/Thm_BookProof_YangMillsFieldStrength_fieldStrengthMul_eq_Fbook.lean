-- Prove2me | Theorems.Thm_BookProof_YangMillsFieldStrength_fieldStrengthMul_eq_Fbook
-- name    : BookProof.YangMillsFieldStrength.fieldStrengthMul_eq_Fbook
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:53:18.184107+00:00
-- url     : https://prove2.me/theorems/b643740c-88e8-4d57-a8e1-65b383fe0798
-- title:
--   Bridge between the two normalizations.** Substituting the book's connection `a_j = -i g A_j` into the abstract field strength `fieldStrengthMul` yields exactly `-i g` times the book's fiel
-- statement:
--   **Bridge between the two normalizations.**  Substituting the book's
--   connection `a_j = -i g A_j` into the abstract field strength `fieldStrengthMul`
--   yields exactly `-i g` times the book's field-strength combination `Fbook`.  So
--   the abstract and the physical normalizations agree up to the coupling.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.YangMillsFieldStrength.fieldStrengthMul_eq_Fbook` (module `BookProof.YangMillsFieldStrength`), line-linked source: `ChapterYangMillsFieldStrength.lean` lines 126–137.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFieldStrength.lean#L126-L137

-- Generated from ChapterYangMillsFieldStrength.lean — theorem BookProof.YangMillsFieldStrength.fieldStrengthMul_eq_Fbook
import Mathlib
import Definitions.Def_ChapterYangMillsFieldStrength
open BookProof.YangMillsFieldStrength













open Complex



variable {R : Type*} [Ring R]









variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem BookProof.YangMillsFieldStrength.fieldStrengthMul_eq_Fbook
    (δ : Fin 3 → R → R) (g : ℝ) (A : Fin 3 → R)
    (hsmul : ∀ (j : Fin 3) (c : ℂ) x, δ j (c • x) = c • δ j x) (j k : Fin 3) :
    fieldStrengthMul δ (fun j => (-(I * (g : ℂ))) • A j) j k
      = (-(I * (g : ℂ))) • Fbook δ g A j k := by sorry
