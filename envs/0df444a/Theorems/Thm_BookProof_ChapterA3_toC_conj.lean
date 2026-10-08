-- Prove2me | Theorems.Thm_BookProof_ChapterA3_toC_conj
-- name    : BookProof.ChapterA3.toC_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:16:28.89811+00:00
-- url     : https://prove2.me/theorems/495eff12-5bd5-4ec8-b2e2-b97bec5a2b44
-- title:
--   `BookProof.ChapterA3.toC_conj` (M : Matrix (Fin 4) (Fin 4) ℝ) : (toC M).map (starRingEnd ℂ) = toC M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3b`.
--
--   `BookProof.ChapterA3.toC_conj` (M : Matrix (Fin 4) (Fin 4) ℝ) : (toC M).map (starRingEnd ℂ) = toC M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.toC_conj`.

-- Generated from ChapterA3b.lean — theorem BookProof.ChapterA3.toC_conj
import Mathlib
import Definitions.Def_ChapterA3b
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.toC_conj (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (toC M).map (starRingEnd ℂ) = toC M := by sorry
