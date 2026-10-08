-- Prove2me | Theorems.Thm_BookProof_ChapterF4_countsketch_unbiased
-- name    : BookProof.ChapterF4.countsketch_unbiased
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:50:32.600475+00:00
-- url     : https://prove2.me/theorems/b8d7b582-5afb-47ff-a88e-ad78a5a3d851
-- title:
--   `BookProof.ChapterF4.countsketch_unbiased` (h : Fin d → Fin k) (x y : Fin d → ℝ) : expectation (fun ω => ∑ j, csketch h ω x j * csketch h ω y j) = ∑ c, x c * y c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF4`.
--
--   `BookProof.ChapterF4.countsketch_unbiased` (h : Fin d → Fin k) (x y : Fin d → ℝ) : expectation (fun ω => ∑ j, csketch h ω x j * csketch h ω y j) = ∑ c, x c * y c
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF4.countsketch_unbiased`.

-- Generated from ChapterF4.lean — theorem BookProof.ChapterF4.countsketch_unbiased
import Mathlib
import Definitions.Def_ChapterF4
import Definitions.Def_ChapterObservableOperator
import Definitions.Def_ChapterScaledDotProduct
open BookProof.ChapterObservableOperator
open BookProof.ChapterScaledDotProduct
open BookProof.ChapterF4


open scoped BigOperators Matrix

variable {d k : ℕ}

theorem BookProof.ChapterF4.countsketch_unbiased (h : Fin d → Fin k) (x y : Fin d → ℝ) :
    expectation (fun ω => ∑ j, csketch h ω x j * csketch h ω y j) = ∑ c, x c * y c := by sorry
