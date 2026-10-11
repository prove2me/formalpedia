-- Prove2me | Theorems.Thm_BookProof_ChapterWignerSymmetry_map_zero
-- name    : BookProof.ChapterWignerSymmetry.map_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T18:16:56.645376+00:00
-- url     : https://prove2.me/theorems/a29174d7-0fc3-4da0-9adb-c956a8d12f28
-- title:
--   `BookProof.ChapterWignerSymmetry.map_zero` (hT : IsWignerSymmetry T) : T 0 = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerSymmetry`.
--
--   `BookProof.ChapterWignerSymmetry.map_zero` (hT : IsWignerSymmetry T) : T 0 = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerSymmetry.map_zero`.

-- Generated from ChapterWignerSymmetry.lean — theorem BookProof.ChapterWignerSymmetry.map_zero
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
open BookProof.ChapterWignerSymmetry


open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

theorem BookProof.ChapterWignerSymmetry.map_zero (hT : IsWignerSymmetry T) : T 0 = 0 := by sorry
