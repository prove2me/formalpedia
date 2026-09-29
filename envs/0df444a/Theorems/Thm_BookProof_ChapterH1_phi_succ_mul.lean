-- Prove2me | Theorems.Thm_BookProof_ChapterH1_phi_succ_mul
-- name    : BookProof.ChapterH1.phi_succ_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:38:09.030162+00:00
-- url     : https://prove2.me/theorems/18aabf0a-dfd0-4c89-a209-b6d2eadade4f
-- title:
--   (k : ℕ) (z : ℂ) : z * phi (k + 1) z = phi k z - 1 / k.factorial
-- statement:
--   Lean 4 theorem `BookProof.ChapterH1.phi_succ_mul` (module `BookProof.ChapterH1`), source chapter `BookProof/ChapterChapterH1.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH1.lean

-- Generated from ChapterH1.lean — theorem BookProof.ChapterH1.phi_succ_mul
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1






open scoped BigOperators
open intervalIntegral


noncomputable section

theorem BookProof.ChapterH1.phi_succ_mul (k : ℕ) (z : ℂ) :
    z * phi (k + 1) z = phi k z - 1 / k.factorial := by sorry
