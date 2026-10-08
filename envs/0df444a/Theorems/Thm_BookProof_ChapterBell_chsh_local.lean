-- Prove2me | Theorems.Thm_BookProof_ChapterBell_chsh_local
-- name    : BookProof.ChapterBell.chsh_local
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:54:10.325994+00:00
-- url     : https://prove2.me/theorems/18621986-0008-45ae-8235-1d5253a0a2f7
-- title:
--   `BookProof.ChapterBell.chsh_local` (μ : Measure Ω) [IsProbabilityMeasure μ] (A₀ A₁ B₀ B₁ : Ω → ℝ) (bA₀ : ∀ ω, |A₀ ω| ≤ 1) (bA₁ : ∀ ω, |A₁ ω| ≤ 1) (bB₀ : ∀...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBell`.
--
--   `BookProof.ChapterBell.chsh_local` (μ : Measure Ω) [IsProbabilityMeasure μ] (A₀ A₁ B₀ B₁ : Ω → ℝ) (bA₀ : ∀ ω, |A₀ ω| ≤ 1) (bA₁ : ∀ ω, |A₁ ω| ≤ 1) (bB₀ : ∀ ω, |B₀ ω| ≤ 1) (bB₁ : ∀ ω, |B₁ ω| ≤ 1) : |∫ ω, (A₀ ω * B₀ ω + A₀ ω * B₁ ω + A₁ ω * B₀ ω - A₁ ω * B₁ ω) ∂μ| ≤ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBell.chsh_local`.

-- Generated from ChapterBell.lean — theorem BookProof.ChapterBell.chsh_local
import Mathlib
import Definitions.Def_ChapterBell
open BookProof.ChapterBell


open scoped BigOperators
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.ChapterBell.chsh_local
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A₀ A₁ B₀ B₁ : Ω → ℝ)
    (bA₀ : ∀ ω, |A₀ ω| ≤ 1) (bA₁ : ∀ ω, |A₁ ω| ≤ 1)
    (bB₀ : ∀ ω, |B₀ ω| ≤ 1) (bB₁ : ∀ ω, |B₁ ω| ≤ 1) :
    |∫ ω, (A₀ ω * B₀ ω + A₀ ω * B₁ ω + A₁ ω * B₀ ω - A₁ ω * B₁ ω) ∂μ| ≤ 2 := by sorry
