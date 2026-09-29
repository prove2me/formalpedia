-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_J_annih
-- name    : BookProof.ChapterParityMajoranaQuant.J_annih
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:45:32.619064+00:00
-- url     : https://prove2.me/theorems/19c21155-3347-4f32-b438-a1807e75dbe9
-- title:
--   The annihilation combinations lie in the `−i`-eigenspace of `J`: `J · annihProj = (−i)·annihProj`
-- statement:
--   The annihilation combinations lie in the `−i`-eigenspace of `J`:
--   `J · annihProj = (−i)·annihProj`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.J_annih` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 154–162.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L154-L162

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.J_annih
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.J_annih (hJ2 : J * J = -1) : J * annihProj J = (-Complex.I) • annihProj J := by sorry
