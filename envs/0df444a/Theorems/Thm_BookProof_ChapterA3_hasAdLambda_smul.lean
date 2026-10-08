-- Prove2me | Theorems.Thm_BookProof_ChapterA3_hasAdLambda_smul
-- name    : BookProof.ChapterA3.hasAdLambda_smul
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T17:45:19.524665+00:00
-- url     : https://prove2.me/theorems/c3ffcc58-5cda-4c71-9b6f-d076041d802b
-- title:
--   `BookProof.ChapterA3.hasAdLambda_smul` {G A : Matrix (Fin 4) (Fin 4) ℝ} (c : ℝ) (h : HasAdLambda G A) : HasAdLambda (c • G) (c • A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3e`.
--
--   `BookProof.ChapterA3.hasAdLambda_smul` {G A : Matrix (Fin 4) (Fin 4) ℝ} (c : ℝ) (h : HasAdLambda G A) : HasAdLambda (c • G) (c • A)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.hasAdLambda_smul`.

-- Generated from ChapterA3e.lean — theorem BookProof.ChapterA3.hasAdLambda_smul
import Mathlib
import Definitions.Def_ChapterA3e
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix

theorem BookProof.ChapterA3.hasAdLambda_smul {G A : Matrix (Fin 4) (Fin 4) ℝ} (c : ℝ)
    (h : HasAdLambda G A) : HasAdLambda (c • G) (c • A) := by sorry
