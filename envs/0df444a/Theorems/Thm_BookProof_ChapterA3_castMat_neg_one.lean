-- Prove2me | Theorems.Thm_BookProof_ChapterA3_castMat_neg_one
-- name    : BookProof.ChapterA3.castMat_neg_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:37:01.539095+00:00
-- url     : https://prove2.me/theorems/dbd105b7-47d7-4cf7-a062-a242b2c8e909
-- title:
--   `BookProof.ChapterA3.castMat_neg_one` : (Int.castRingHom ℝ).mapMatrix (-1 : Matrix (Fin 4) (Fin 4) ℤ) = -1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3d`.
--
--   `BookProof.ChapterA3.castMat_neg_one` : (Int.castRingHom ℝ).mapMatrix (-1 : Matrix (Fin 4) (Fin 4) ℤ) = -1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.castMat_neg_one`.

-- Generated from ChapterA3d.lean — theorem BookProof.ChapterA3.castMat_neg_one
import Mathlib
import Definitions.Def_ChapterA3d
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.castMat_neg_one :
    (Int.castRingHom ℝ).mapMatrix (-1 : Matrix (Fin 4) (Fin 4) ℤ) = -1 := by sorry
