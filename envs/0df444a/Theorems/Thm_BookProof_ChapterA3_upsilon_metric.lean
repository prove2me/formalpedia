-- Prove2me | Theorems.Thm_BookProof_ChapterA3_upsilon_metric
-- name    : BookProof.ChapterA3.upsilon_metric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T13:08:25.373976+00:00
-- url     : https://prove2.me/theorems/e4d1faec-91db-427a-a80d-6e3c01c9401d
-- title:
--   `BookProof.ChapterA3.upsilon_metric` (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) : (Upsilon T)ᵀ * minkowskiMat * Upsilon T = minkowskiMat
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.upsilon_metric` (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) : (Upsilon T)ᵀ * minkowskiMat * Upsilon T = minkowskiMat
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.upsilon_metric`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.upsilon_metric
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.upsilon_metric (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) :
    (Upsilon T)ᵀ * minkowskiMat * Upsilon T = minkowskiMat := by sorry
