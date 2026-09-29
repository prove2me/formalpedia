-- Prove2me | Theorems.Thm_BookProof_ChapterSirkGramCutoff_synthesis_isometry_of_orthonormal
-- name    : BookProof.ChapterSirkGramCutoff.synthesis_isometry_of_orthonormal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T05:22:28.739517+00:00
-- url     : https://prove2.me/theorems/15082014-fa6d-4bca-8c78-4e5570075dc4
-- title:
--   {d : ℕ} {v : Fin d → E} (hv : Orthonormal ℂ v) : (adjoint (synthesis v)).comp (synthesis v) = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d))
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkGramCutoff.synthesis_isometry_of_orthonormal` (module `BookProof.ChapterSirkGramCutoff`), source chapter `BookProof/ChapterChapterSirkGramCutoff.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterSirkGramCutoff.lean

-- Generated from ChapterSirkGramCutoff.lean — theorem BookProof.ChapterSirkGramCutoff.synthesis_isometry_of_orthonormal
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
open BookProof.ChapterSirkGramCutoff









noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

theorem BookProof.ChapterSirkGramCutoff.synthesis_isometry_of_orthonormal {d : ℕ} {v : Fin d → E} (hv : Orthonormal ℂ v) :
    (adjoint (synthesis v)).comp (synthesis v)
      = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)) := by sorry
