-- Prove2me | Theorems.Thm_BookProof_ChapterH1_psi_resolvent
-- name    : BookProof.ChapterH1.psi_resolvent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:18:15.242664+00:00
-- url     : https://prove2.me/theorems/caea79dc-8c43-475b-99ff-4a4a5c6a8c10
-- title:
--   (k : ℕ) (γ z : ℂ) (_hz : γ - z ≠ 0) : psi k γ (γ - z)⁻¹ = phi k z
-- statement:
--   Lean 4 theorem `BookProof.ChapterH1.psi_resolvent` (module `BookProof.ChapterH1`), source chapter `BookProof/ChapterChapterH1.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterH1.lean

-- Generated from ChapterH1.lean — theorem BookProof.ChapterH1.psi_resolvent
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1






open scoped BigOperators
open intervalIntegral


noncomputable section














variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterH1.psi_resolvent (k : ℕ) (γ z : ℂ) (_hz : γ - z ≠ 0) :
    psi k γ (γ - z)⁻¹ = phi k z := by sorry
