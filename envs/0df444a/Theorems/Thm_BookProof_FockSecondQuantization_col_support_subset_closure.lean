-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_col_support_subset_closure
-- name    : BookProof.FockSecondQuantization.col_support_subset_closure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:16:18.49945+00:00
-- url     : https://prove2.me/theorems/fe46c843-f6dd-442c-b9d1-1f345f830196
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) : ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ closureModes col u v
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.col_support_subset_closure` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.col_support_subset_closure
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.col_support_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ closureModes col u v := by sorry
