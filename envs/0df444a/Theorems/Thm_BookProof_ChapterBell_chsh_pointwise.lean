-- Prove2me | Theorems.Thm_BookProof_ChapterBell_chsh_pointwise
-- name    : BookProof.ChapterBell.chsh_pointwise
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:53:58.468223+00:00
-- url     : https://prove2.me/theorems/49cb3ffc-7bba-4483-8e0f-ba83debd05c7
-- title:
--   `BookProof.ChapterBell.chsh_pointwise` {a₀ a₁ b₀ b₁ : ℝ} (ha₀ : |a₀| ≤ 1) (ha₁ : |a₁| ≤ 1) (hb₀ : |b₀| ≤ 1) (hb₁ : |b₁| ≤ 1) : |a₀ * b₀ + a₀ * b₁ + a₁...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBell`.
--
--   `BookProof.ChapterBell.chsh_pointwise` {a₀ a₁ b₀ b₁ : ℝ} (ha₀ : |a₀| ≤ 1) (ha₁ : |a₁| ≤ 1) (hb₀ : |b₀| ≤ 1) (hb₁ : |b₁| ≤ 1) : |a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁| ≤ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBell.chsh_pointwise`.

-- Generated from ChapterBell.lean — theorem BookProof.ChapterBell.chsh_pointwise
import Mathlib
import Definitions.Def_ChapterBell
open BookProof.ChapterBell


open scoped BigOperators
open MeasureTheory

theorem BookProof.ChapterBell.chsh_pointwise {a₀ a₁ b₀ b₁ : ℝ}
    (ha₀ : |a₀| ≤ 1) (ha₁ : |a₁| ≤ 1) (hb₀ : |b₀| ≤ 1) (hb₁ : |b₁| ≤ 1) :
    |a₀ * b₀ + a₀ * b₁ + a₁ * b₀ - a₁ * b₁| ≤ 2 := by sorry
