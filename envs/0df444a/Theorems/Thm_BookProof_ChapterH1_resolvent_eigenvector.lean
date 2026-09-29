-- Prove2me | Theorems.Thm_BookProof_ChapterH1_resolvent_eigenvector
-- name    : BookProof.ChapterH1.resolvent_eigenvector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:38:55.605419+00:00
-- url     : https://prove2.me/theorems/3b232e91-5da5-49c3-a194-504e94080bd8
-- title:
--   {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (T : F →L[ℂ] F) (X : F →L[ℂ] F) (γ z : ℂ) (v : F) (hTv : T v = z • v) (hz : γ - z ≠ 0) (_hXr : (γ • (1 : F →L[ℂ] F) - T) * X = 1) (hXl : X *...
-- statement:
--   Lean 4 theorem `BookProof.ChapterH1.resolvent_eigenvector` (module `BookProof.ChapterH1`), source chapter `BookProof/ChapterChapterH1.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH1.lean

-- Generated from ChapterH1.lean — theorem BookProof.ChapterH1.resolvent_eigenvector
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1






open scoped BigOperators
open intervalIntegral


noncomputable section














variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterH1.resolvent_eigenvector {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : F →L[ℂ] F) (X : F →L[ℂ] F) (γ z : ℂ) (v : F)
    (hTv : T v = z • v) (hz : γ - z ≠ 0)
    (_hXr : (γ • (1 : F →L[ℂ] F) - T) * X = 1)
    (hXl : X * (γ • (1 : F →L[ℂ] F) - T) = 1) :
    X v = (γ - z)⁻¹ • v := by sorry
