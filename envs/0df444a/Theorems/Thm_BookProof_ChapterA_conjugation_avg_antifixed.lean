-- Prove2me | Theorems.Thm_BookProof_ChapterA_conjugation_avg_antifixed
-- name    : BookProof.ChapterA.conjugation_avg_antifixed
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T04:38:43.714985+00:00
-- url     : https://prove2.me/theorems/989e7673-ec88-4ee9-8bb0-0e652732d730
-- title:
--   `BookProof.ChapterA.conjugation_avg_antifixed` (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = x) (x : V) : θ ((2⁻¹ : ℂ) • (x - θ x)) = -((2⁻¹ : ℂ) • (x - θ x))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1`.
--
--   `BookProof.ChapterA.conjugation_avg_antifixed` (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = x) (x : V) : θ ((2⁻¹ : ℂ) • (x - θ x)) = -((2⁻¹ : ℂ) • (x - θ x))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.conjugation_avg_antifixed`.

-- Generated from ChapterA1.lean — theorem BookProof.ChapterA.conjugation_avg_antifixed
import Mathlib
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

theorem BookProof.ChapterA.conjugation_avg_antifixed (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = x) (x : V) :
    θ ((2⁻¹ : ℂ) • (x - θ x)) = -((2⁻¹ : ℂ) • (x - θ x)) := by sorry
