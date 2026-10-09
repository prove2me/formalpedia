-- Prove2me | Theorems.Thm_BookProof_ChapterA3_fixesNullAxis_iff_conj
-- name    : BookProof.ChapterA3.fixesNullAxis_iff_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:10:56.259119+00:00
-- url     : https://prove2.me/theorems/dfe266e2-ac42-41f2-989f-f5f01b3e1a74
-- title:
--   `BookProof.ChapterA3.fixesNullAxis_iff_conj` (T : Matrix (Fin 2) (Fin 2) ℂ) : FixesNullAxis (Upsilon T) ↔ Tᴴ * (pauliσ 0 + pauliσ 3) * T = pauliσ 0 + pauliσ 3
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4d`.
--
--   `BookProof.ChapterA3.fixesNullAxis_iff_conj` (T : Matrix (Fin 2) (Fin 2) ℂ) : FixesNullAxis (Upsilon T) ↔ Tᴴ * (pauliσ 0 + pauliσ 3) * T = pauliσ 0 + pauliσ 3
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.fixesNullAxis_iff_conj`.

-- Generated from ChapterA4d.lean — theorem BookProof.ChapterA3.fixesNullAxis_iff_conj
import Mathlib
import Definitions.Def_ChapterA4d
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.fixesNullAxis_iff_conj (T : Matrix (Fin 2) (Fin 2) ℂ) :
    FixesNullAxis (Upsilon T) ↔ Tᴴ * (pauliσ 0 + pauliσ 3) * T = pauliσ 0 + pauliσ 3 := by sorry
