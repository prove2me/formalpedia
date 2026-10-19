-- Prove2me | Theorems.Thm_BookProof_ChapterA_conjCLM_unitScale
-- name    : BookProof.ChapterA.conjCLM_unitScale
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:18:49.718986+00:00
-- url     : https://prove2.me/theorems/389682bc-5bb4-4f6c-8652-35ea5368782d
-- title:
--   `BookProof.ChapterA.conjCLM_unitScale` (α : V ≃ₗᵢ[ℂ] W) (l : ℂ) (hl : ‖l‖ = 1) (m : V →L[ℂ] V) : conjCLM (α.trans (unitScaleEquiv l hl)) m = conjCLM α m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2d`.
--
--   `BookProof.ChapterA.conjCLM_unitScale` (α : V ≃ₗᵢ[ℂ] W) (l : ℂ) (hl : ‖l‖ = 1) (m : V →L[ℂ] V) : conjCLM (α.trans (unitScaleEquiv l hl)) m = conjCLM α m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.conjCLM_unitScale`.

-- Generated from ChapterA2d.lean — theorem BookProof.ChapterA.conjCLM_unitScale
import Mathlib
import Definitions.Def_ChapterA2d
import Definitions.Def_ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

theorem BookProof.ChapterA.conjCLM_unitScale (α : V ≃ₗᵢ[ℂ] W) (l : ℂ) (hl : ‖l‖ = 1) (m : V →L[ℂ] V) :
    conjCLM (α.trans (unitScaleEquiv l hl)) m = conjCLM α m := by sorry
