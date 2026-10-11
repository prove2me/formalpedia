-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_ip_smul_right
-- name    : BookProof.ChapterWeakValue.ip_smul_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:11:26.078982+00:00
-- url     : https://prove2.me/theorems/e838f164-33b8-4104-8c4c-22ffa4d041b2
-- title:
--   `BookProof.ChapterWeakValue.ip_smul_right` (c : ℂ) (f v : Fin n → ℂ) : ip f (c • v) = c * ip f v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.ip_smul_right` (c : ℂ) (f v : Fin n → ℂ) : ip f (c • v) = c * ip f v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.ip_smul_right`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.ip_smul_right
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.ip_smul_right (c : ℂ) (f v : Fin n → ℂ) : ip f (c • v) = c * ip f v := by sorry
