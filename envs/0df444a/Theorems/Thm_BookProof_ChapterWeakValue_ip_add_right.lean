-- Prove2me | Theorems.Thm_BookProof_ChapterWeakValue_ip_add_right
-- name    : BookProof.ChapterWeakValue.ip_add_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:11:12.1451+00:00
-- url     : https://prove2.me/theorems/4c9a71d6-2a1e-485c-aa61-267a63742a8a
-- title:
--   `BookProof.ChapterWeakValue.ip_add_right` (f v w : Fin n → ℂ) : ip f (v + w) = ip f v + ip f w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeakValue`.
--
--   `BookProof.ChapterWeakValue.ip_add_right` (f v w : Fin n → ℂ) : ip f (v + w) = ip f v + ip f w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeakValue.ip_add_right`.

-- Generated from ChapterWeakValue.lean — theorem BookProof.ChapterWeakValue.ip_add_right
import Mathlib
import Definitions.Def_ChapterWeakValue
open BookProof.ChapterWeakValue


open scoped BigOperators Matrix


variable {n : ℕ}

theorem BookProof.ChapterWeakValue.ip_add_right (f v w : Fin n → ℂ) : ip f (v + w) = ip f v + ip f w := by sorry
