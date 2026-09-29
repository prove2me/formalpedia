-- Prove2me | Theorems.Thm_BookProof_YangMillsFieldStrength_Fbook_antisymm
-- name    : BookProof.YangMillsFieldStrength.Fbook_antisymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:52:07.419183+00:00
-- url     : https://prove2.me/theorems/8ebd26cb-4351-4049-a03b-52f00f7ac3bc
-- title:
--   The book's field strength is antisymmetric: `F^{book}_{j k} = - F^{book}_{k j}`
-- statement:
--   The book's field strength is antisymmetric: `F^{book}_{j k} = - F^{book}_{k j}`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.YangMillsFieldStrength.Fbook_antisymm` (module `BookProof.YangMillsFieldStrength`), line-linked source: `ChapterYangMillsFieldStrength.lean` lines 162–165.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFieldStrength.lean#L162-L165

-- Generated from ChapterYangMillsFieldStrength.lean — theorem BookProof.YangMillsFieldStrength.Fbook_antisymm
import Mathlib
import Definitions.Def_ChapterYangMillsFieldStrength
open BookProof.YangMillsFieldStrength













open Complex



variable {R : Type*} [Ring R]









variable {R : Type*} [Ring R] [Algebra ℂ R]

theorem BookProof.YangMillsFieldStrength.Fbook_antisymm (δ : Fin 3 → R → R) (g : ℝ) (A : Fin 3 → R) (j k : Fin 3) :
    Fbook δ g A j k = - Fbook δ g A k j := by sorry
