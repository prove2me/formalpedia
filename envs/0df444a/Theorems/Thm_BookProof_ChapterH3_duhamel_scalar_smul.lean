-- Prove2me | Theorems.Thm_BookProof_ChapterH3_duhamel_scalar_smul
-- name    : BookProof.ChapterH3.duhamel_scalar_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:53:14.704638+00:00
-- url     : https://prove2.me/theorems/40fa57c1-451e-4c02-925b-25c9e7456b34
-- title:
--   `BookProof.ChapterH3.duhamel_scalar_smul` (z g : ℂ) (δ : ℝ) : (∫ s in (0:ℝ)..δ, Complex.exp ((↑(δ - s)) * z) * g) = δ * BookProof.ChapterH1.phi 1 (δ * z) * g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterH3`.
--
--   `BookProof.ChapterH3.duhamel_scalar_smul` (z g : ℂ) (δ : ℝ) : (∫ s in (0:ℝ)..δ, Complex.exp ((↑(δ - s)) * z) * g) = δ * BookProof.ChapterH1.phi 1 (δ * z) * g
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterH3.duhamel_scalar_smul`.

-- Generated from ChapterH3.lean — theorem BookProof.ChapterH3.duhamel_scalar_smul
import Mathlib
import Definitions.Def_ChapterH3
import Definitions.Def_ChapterH1
open BookProof.ChapterH1
open BookProof.ChapterH3


open scoped BigOperators
open intervalIntegral


noncomputable section

theorem BookProof.ChapterH3.duhamel_scalar_smul (z g : ℂ) (δ : ℝ) :
    (∫ s in (0:ℝ)..δ, Complex.exp ((↑(δ - s)) * z) * g)
      = δ * BookProof.ChapterH1.phi 1 (δ * z) * g := by sorry
