-- Prove2me | Theorems.Thm_BookProof_ChapterA3_bilC_minkowski
-- name    : BookProof.ChapterA3.bilC_minkowski
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:53:03.48+00:00
-- url     : https://prove2.me/theorems/a2cae159-9061-4421-a92e-94d4e45d3cb9
-- title:
--   `BookProof.ChapterA3.bilC_minkowski` (x : Fin 4 → ℂ) : bilC (toC minkowskiMat) x = Qc x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.bilC_minkowski` (x : Fin 4 → ℂ) : bilC (toC minkowskiMat) x = Qc x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.bilC_minkowski`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.bilC_minkowski
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.bilC_minkowski (x : Fin 4 → ℂ) : bilC (toC minkowskiMat) x = Qc x := by sorry
