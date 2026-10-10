-- Prove2me | Theorems.Thm_BookProof_ChapterH3_duhamel_scalar
-- name    : BookProof.ChapterH3.duhamel_scalar
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:52:35.541293+00:00
-- url     : https://prove2.me/theorems/80848d37-7c27-40f9-a4af-809c3985705b
-- title:
--   `BookProof.ChapterH3.duhamel_scalar` (z : ℂ) (δ : ℝ) : (∫ s in (0:ℝ)..δ, Complex.exp ((↑(δ - s)) * z)) = δ * BookProof.ChapterH1.phi 1 (δ * z)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH3`.
--
--   `BookProof.ChapterH3.duhamel_scalar` (z : ℂ) (δ : ℝ) : (∫ s in (0:ℝ)..δ, Complex.exp ((↑(δ - s)) * z)) = δ * BookProof.ChapterH1.phi 1 (δ * z)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH3.duhamel_scalar`.

-- Generated from ChapterH3.lean — theorem BookProof.ChapterH3.duhamel_scalar
import Mathlib
import Definitions.Def_ChapterH3
import Definitions.Def_ChapterH1
open BookProof.ChapterH1
open BookProof.ChapterH3


open scoped BigOperators
open intervalIntegral


noncomputable section

theorem BookProof.ChapterH3.duhamel_scalar (z : ℂ) (δ : ℝ) :
    (∫ s in (0:ℝ)..δ, Complex.exp ((↑(δ - s)) * z))
      = δ * BookProof.ChapterH1.phi 1 (δ * z) := by sorry
