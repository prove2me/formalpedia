-- Prove2me | Theorems.Thm_BookProof_ChapterF4_csketch_smul
-- name    : BookProof.ChapterF4.csketch_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T03:49:48.335515+00:00
-- url     : https://prove2.me/theorems/43023489-dc43-4301-9b87-c5e50a7a5fb6
-- title:
--   `BookProof.ChapterF4.csketch_smul` (h : Fin d → Fin k) (ω : Fin d → Bool) (a : ℝ) (x : Fin d → ℝ) : csketch h ω (a • x) = a • csketch h ω x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.csketch_smul` (h : Fin d → Fin k) (ω : Fin d → Bool) (a : ℝ) (x : Fin d → ℝ) : csketch h ω (a • x) = a • csketch h ω x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.csketch_smul`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.csketch_smul
import Mathlib
import Definitions.Def_ChapterF4
import Definitions.Def_ChapterScaledDotProduct
open BookProof.ChapterScaledDotProduct
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}

theorem BookProof.ChapterF4.csketch_smul (h : Fin d → Fin k) (ω : Fin d → Bool) (a : ℝ) (x : Fin d → ℝ) :
    csketch h ω (a • x) = a • csketch h ω x := by sorry
