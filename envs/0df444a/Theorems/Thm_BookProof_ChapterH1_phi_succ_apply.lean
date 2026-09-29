-- Prove2me | Theorems.Thm_BookProof_ChapterH1_phi_succ_apply
-- name    : BookProof.ChapterH1.phi_succ_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:16:24.782457+00:00
-- url     : https://prove2.me/theorems/41b24a97-429a-44bd-b965-ca69b10c968f
-- title:
--   (k : ℕ) (z : ℂ) : phi (k + 1) z = ∫ s in (0 : ℝ)..1, Complex.exp (s * z) * (1 - s) ^ k / k.factorial
-- statement:
--   Lean 4 theorem `BookProof.ChapterH1.phi_succ_apply` (module `BookProof.ChapterH1`), source chapter `BookProof/ChapterChapterH1.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH1.lean

-- Generated from ChapterH1.lean — theorem BookProof.ChapterH1.phi_succ_apply
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1






open scoped BigOperators
open intervalIntegral


noncomputable section

theorem BookProof.ChapterH1.phi_succ_apply (k : ℕ) (z : ℂ) :
    phi (k + 1) z = ∫ s in (0 : ℝ)..1, Complex.exp (s * z) * (1 - s) ^ k / k.factorial := by sorry
