-- Prove2me | Theorems.Thm_BookProof_ChapterA3_isPin_neg
-- name    : BookProof.ChapterA3.isPin_neg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T12:33:37.849004+00:00
-- url     : https://prove2.me/theorems/ea3545bf-4cb8-42c7-8dc6-5076852e6b81
-- title:
--   `BookProof.ChapterA3.isPin_neg` {S : Matrix (Fin 4) (Fin 4) ℝ} (h : IsPin S) : IsPin (-S)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3c`.
--
--   `BookProof.ChapterA3.isPin_neg` {S : Matrix (Fin 4) (Fin 4) ℝ} (h : IsPin S) : IsPin (-S)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3.isPin_neg`.

-- Generated from ChapterA3c.lean — theorem BookProof.ChapterA3.isPin_neg
import Mathlib
import Definitions.Def_ChapterA3c
import Definitions.Def_ChapterA3
open BookProof.ChapterA3


open Matrix
open scoped ComplexConjugate

theorem BookProof.ChapterA3.isPin_neg {S : Matrix (Fin 4) (Fin 4) ℝ} (h : IsPin S) : IsPin (-S) := by sorry
