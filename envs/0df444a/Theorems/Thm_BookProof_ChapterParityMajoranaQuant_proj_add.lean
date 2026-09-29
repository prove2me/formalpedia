-- Prove2me | Theorems.Thm_BookProof_ChapterParityMajoranaQuant_proj_add
-- name    : BookProof.ChapterParityMajoranaQuant.proj_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:49:37.251714+00:00
-- url     : https://prove2.me/theorems/aae7294d-954d-4c7e-a48b-965fd6453b71
-- title:
--   The field split `a(v) = a(v+iJv) + a(v−iJv)`: the two projections sum to the identity
-- statement:
--   The field split `a(v) = a(v+iJv) + a(v−iJv)`: the two projections sum to the identity.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.ChapterParityMajoranaQuant.proj_add` (module `BookProof.ParityMajoranaQuant`), line-linked source: `ChapterParityMajoranaQuant.lean` lines 85–90.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterParityMajoranaQuant.lean#L85-L90

-- Generated from ChapterParityMajoranaQuant.lean — theorem BookProof.ChapterParityMajoranaQuant.proj_add
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant










open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

theorem BookProof.ChapterParityMajoranaQuant.proj_add : annihProj J + creatProj J = 1 := by sorry
