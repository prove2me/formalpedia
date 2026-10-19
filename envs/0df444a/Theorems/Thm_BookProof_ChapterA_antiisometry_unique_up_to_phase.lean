-- Prove2me | Theorems.Thm_BookProof_ChapterA_antiisometry_unique_up_to_phase
-- name    : BookProof.ChapterA.antiisometry_unique_up_to_phase
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:13:14.652968+00:00
-- url     : https://prove2.me/theorems/f796e2d6-78ec-4077-b1da-3d5773d64ae9
-- title:
--   `BookProof.ChapterA.antiisometry_unique_up_to_phase` (M : System ℂ V) (hSchur : IsSchurUnitary M) {θ₁ θ₂ : AntiUnitary V} (h₁ : CommutesAntiUnitary M θ₁) (h₂ : CommutesAntiUnitary
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2`.
--
--   `BookProof.ChapterA.antiisometry_unique_up_to_phase` (M : System ℂ V) (hSchur : IsSchurUnitary M) {θ₁ θ₂ : AntiUnitary V} (h₁ : CommutesAntiUnitary M θ₁) (h₂ : CommutesAntiUnitary M θ₂) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, θ₂ x = c • θ₁ x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.antiisometry_unique_up_to_phase`.

-- Generated from ChapterA2.lean — theorem BookProof.ChapterA.antiisometry_unique_up_to_phase
import Mathlib
import Definitions.Def_ChapterA2
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.antiisometry_unique_up_to_phase (M : System ℂ V) (hSchur : IsSchurUnitary M)
    {θ₁ θ₂ : AntiUnitary V} (h₁ : CommutesAntiUnitary M θ₁) (h₂ : CommutesAntiUnitary M θ₂) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, θ₂ x = c • θ₁ x := by sorry
