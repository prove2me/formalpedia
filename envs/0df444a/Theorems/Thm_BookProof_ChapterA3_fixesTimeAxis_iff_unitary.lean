-- Prove2me | Theorems.Thm_BookProof_ChapterA3_fixesTimeAxis_iff_unitary
-- name    : BookProof.ChapterA3.fixesTimeAxis_iff_unitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:10:11.264829+00:00
-- url     : https://prove2.me/theorems/4e217a26-af44-420c-b467-7fae48c80179
-- title:
--   `BookProof.ChapterA3.fixesTimeAxis_iff_unitary` (T : Matrix (Fin 2) (Fin 2) ℂ) : FixesTimeAxis (Upsilon T) ↔ Tᴴ * T = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA4c`.
--
--   `BookProof.ChapterA3.fixesTimeAxis_iff_unitary` (T : Matrix (Fin 2) (Fin 2) ℂ) : FixesTimeAxis (Upsilon T) ↔ Tᴴ * T = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.fixesTimeAxis_iff_unitary`.

-- Generated from ChapterA4c.lean — theorem BookProof.ChapterA3.fixesTimeAxis_iff_unitary
import Mathlib
import Definitions.Def_ChapterA4c
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.fixesTimeAxis_iff_unitary (T : Matrix (Fin 2) (Fin 2) ℂ) :
    FixesTimeAxis (Upsilon T) ↔ Tᴴ * T = 1 := by sorry
