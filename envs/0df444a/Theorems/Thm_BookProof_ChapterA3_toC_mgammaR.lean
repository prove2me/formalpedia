-- Prove2me | Theorems.Thm_BookProof_ChapterA3_toC_mgammaR
-- name    : BookProof.ChapterA3.toC_mgammaR
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:19:54.776322+00:00
-- url     : https://prove2.me/theorems/e93de690-4d6b-4e0e-8f56-64808073ce4d
-- title:
--   `BookProof.ChapterA3.toC_mgammaR` (μ : Fin 4) : toC (mgammaR μ) = mgamma μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3c`.
--
--   `BookProof.ChapterA3.toC_mgammaR` (μ : Fin 4) : toC (mgammaR μ) = mgamma μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.toC_mgammaR`.

-- Generated from ChapterA3c.lean — theorem BookProof.ChapterA3.toC_mgammaR
import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3b
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.toC_mgammaR (μ : Fin 4) : toC (mgammaR μ) = mgamma μ := by sorry
