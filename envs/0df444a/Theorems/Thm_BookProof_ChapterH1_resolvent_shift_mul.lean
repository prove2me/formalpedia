-- Prove2me | Theorems.Thm_BookProof_ChapterH1_resolvent_shift_mul
-- name    : BookProof.ChapterH1.resolvent_shift_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:39:02.52699+00:00
-- url     : https://prove2.me/theorems/118ca9c1-ac1f-4ddc-80c1-bda721d1c225
-- title:
--   (a : A) (N h : ℂ) (j m : ℂ) (Xj Xm : A) (_hjl : (algebraMap ℂ A (N - h * j) - a) * Xj = 1) (hjr : Xj * (algebraMap ℂ A (N - h * j) - a) = 1) (hml : (algebraMap ℂ A (N - h * m) - a) * Xm = 1)...
-- statement:
--   Lean 4 theorem `BookProof.ChapterH1.resolvent_shift_mul` (module `BookProof.ChapterH1`), source chapter `BookProof/ChapterChapterH1.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH1.lean

-- Generated from ChapterH1.lean — theorem BookProof.ChapterH1.resolvent_shift_mul
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1






open scoped BigOperators
open intervalIntegral


noncomputable section














variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]








variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem BookProof.ChapterH1.resolvent_shift_mul (a : A) (N h : ℂ) (j m : ℂ)
    (Xj Xm : A)
    (_hjl : (algebraMap ℂ A (N - h * j) - a) * Xj = 1)
    (hjr : Xj * (algebraMap ℂ A (N - h * j) - a) = 1)
    (hml : (algebraMap ℂ A (N - h * m) - a) * Xm = 1)
    (_hmr : Xm * (algebraMap ℂ A (N - h * m) - a) = 1) :
    Xj * (1 + (h * (m - j)) • Xm) = Xm := by sorry
