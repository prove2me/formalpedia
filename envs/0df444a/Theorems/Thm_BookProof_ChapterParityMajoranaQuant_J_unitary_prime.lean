-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_J_unitary_prime
-- name    : BookProof.ChapterParityMajoranaQuant.J_unitary_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T08:18:32.14305+00:00
-- url     : https://prove2.me/theorems/af3fc4ae-f0c2-4c64-b927-600c5593dd8d
-- title:
--   A compatible complex structure is unitary on the other side too: `J · Jᴴ = 1`
-- statement:
--   A compatible complex structure is unitary on the other side too: `J · Jᴴ = 1`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.J_unitary'` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 150–152.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L150-L152

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.J_unitary'
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.J_unitary_prime (hJ2 : J * J = -1) (hskew : Jᴴ = -J) : J * Jᴴ = 1 := by sorry
