-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_inner_toLp
-- name    : BookProof.FockSecondQuantization.inner_toLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:59:10.815709+00:00
-- url     : https://prove2.me/theorems/745f264c-20f3-4a8f-8968-dce8fa49ab0d
-- title:
--   (u v : FockAlg) : (inner ℂ (toLp u) (toLp v) : ℂ) = ∑ α ∈ u.support, (starRingEnd ℂ) (u α) * v α
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.inner_toLp` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.inner_toLp
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.inner_toLp (u v : FockAlg) :
    (inner ℂ (toLp u) (toLp v) : ℂ) = ∑ α ∈ u.support, (starRingEnd ℂ) (u α) * v α := by sorry
