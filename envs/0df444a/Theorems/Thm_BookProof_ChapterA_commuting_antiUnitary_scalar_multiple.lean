-- Prove2me | Theorems.Thm_BookProof_ChapterA_commuting_antiUnitary_scalar_multiple
-- name    : BookProof.ChapterA.commuting_antiUnitary_scalar_multiple
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:13:14.201976+00:00
-- url     : https://prove2.me/theorems/4b2b8c30-cf2f-4e20-967f-64e8dc39b984
-- title:
--   `BookProof.ChapterA.commuting_antiUnitary_scalar_multiple` (M : System ℂ V) (hSchur : IsSchurUnitary M) {θ₁ θ₂ : AntiUnitary V} (h₁ : CommutesAntiUnitary M θ₁) (h₂ : CommutesAntiUn
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2`.
--
--   `BookProof.ChapterA.commuting_antiUnitary_scalar_multiple` (M : System ℂ V) (hSchur : IsSchurUnitary M) {θ₁ θ₂ : AntiUnitary V} (h₁ : CommutesAntiUnitary M θ₁) (h₂ : CommutesAntiUnitary M θ₂) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, θ₂ x = c • θ₁ x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.commuting_antiUnitary_scalar_multiple`.

-- Generated from ChapterA2.lean — theorem BookProof.ChapterA.commuting_antiUnitary_scalar_multiple
import Mathlib
import Definitions.Def_ChapterA2
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.commuting_antiUnitary_scalar_multiple (M : System ℂ V) (hSchur : IsSchurUnitary M)
    {θ₁ θ₂ : AntiUnitary V} (h₁ : CommutesAntiUnitary M θ₁) (h₂ : CommutesAntiUnitary M θ₂) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, θ₂ x = c • θ₁ x := by sorry
