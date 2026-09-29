-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_J_creat
-- name    : BookProof.ChapterParityMajoranaQuant.J_creat
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:46:53.491923+00:00
-- url     : https://prove2.me/theorems/e5eebd91-c675-4c93-af80-1e781cea95d9
-- title:
--   The creation combinations lie in the `+i`-eigenspace of `J`: `J · creatProj = i·creatProj`
-- statement:
--   The creation combinations lie in the `+i`-eigenspace of `J`:
--   `J · creatProj = i·creatProj`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.J_creat` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 164–172.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L164-L172

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.J_creat
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.J_creat (hJ2 : J * J = -1) : J * creatProj J = Complex.I • creatProj J := by sorry
