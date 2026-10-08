-- Prove2me | Theorems.Thm_BookProof_ChapterA3_det_sq_of_sq_neg_one
-- name    : BookProof.ChapterA3.det_sq_of_sq_neg_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:38:12.39717+00:00
-- url     : https://prove2.me/theorems/2a225881-29e9-4882-a4e7-29b7fae7acd7
-- title:
--   `BookProof.ChapterA3.det_sq_of_sq_neg_one` {S : Matrix (Fin 4) (Fin 4) ℝ} (h : S * S = -1) : S.det * S.det = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3d`.
--
--   `BookProof.ChapterA3.det_sq_of_sq_neg_one` {S : Matrix (Fin 4) (Fin 4) ℝ} (h : S * S = -1) : S.det * S.det = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.det_sq_of_sq_neg_one`.

-- Generated from ChapterA3d.lean — theorem BookProof.ChapterA3.det_sq_of_sq_neg_one
import Mathlib
import Definitions.Def_ChapterA3d
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.det_sq_of_sq_neg_one {S : Matrix (Fin 4) (Fin 4) ℝ} (h : S * S = -1) :
    S.det * S.det = 1 := by sorry
