-- Prove2me | Theorems.Thm_BookProof_ChapterA3_upsilonC_metric
-- name    : BookProof.ChapterA3.upsilonC_metric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:54:06.444598+00:00
-- url     : https://prove2.me/theorems/53bf2320-c593-489d-8235-c9f9e89de31d
-- title:
--   `BookProof.ChapterA3.upsilonC_metric` (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) : (UpsilonC T)ᵀ * toC minkowskiMat * UpsilonC T = toC minkowskiMat
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3h`.
--
--   `BookProof.ChapterA3.upsilonC_metric` (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) : (UpsilonC T)ᵀ * toC minkowskiMat * UpsilonC T = toC minkowskiMat
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.upsilonC_metric`.

-- Generated from ChapterA3h.lean — theorem BookProof.ChapterA3.upsilonC_metric
import Mathlib
import Definitions.Def_ChapterA3h
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.upsilonC_metric (T : Matrix (Fin 2) (Fin 2) ℂ) (hT : T.det = 1) :
    (UpsilonC T)ᵀ * toC minkowskiMat * UpsilonC T = toC minkowskiMat := by sorry
