-- Prove2me | Theorems.Thm_BookProof_ChapterA_conjAU_commutesAntiUnitary
-- name    : BookProof.ChapterA.conjAU_commutesAntiUnitary
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:19:10.542992+00:00
-- url     : https://prove2.me/theorems/47ae8ead-2525-4dc2-a618-3c35e4ed0e62
-- title:
--   `BookProof.ChapterA.conjAU_commutesAntiUnitary` {M : System ℂ V} {N : System ℂ W} {α : V ≃ₗᵢ[ℂ] W} (hα : IsSystemIso M N α) {θ : AntiUnitary V} (hθ : CommutesAntiUnitary M θ) : Com
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2d`.
--
--   `BookProof.ChapterA.conjAU_commutesAntiUnitary` {M : System ℂ V} {N : System ℂ W} {α : V ≃ₗᵢ[ℂ] W} (hα : IsSystemIso M N α) {θ : AntiUnitary V} (hθ : CommutesAntiUnitary M θ) : CommutesAntiUnitary N (conjAU α θ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.conjAU_commutesAntiUnitary`.

-- Generated from ChapterA2d.lean — theorem BookProof.ChapterA.conjAU_commutesAntiUnitary
import Mathlib
import Definitions.Def_ChapterA2d
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

theorem BookProof.ChapterA.conjAU_commutesAntiUnitary {M : System ℂ V} {N : System ℂ W} {α : V ≃ₗᵢ[ℂ] W}
    (hα : IsSystemIso M N α) {θ : AntiUnitary V} (hθ : CommutesAntiUnitary M θ) :
    CommutesAntiUnitary N (conjAU α θ) := by sorry
