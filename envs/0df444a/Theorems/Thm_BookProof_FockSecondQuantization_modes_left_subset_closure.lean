-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_modes_left_subset_closure
-- name    : BookProof.FockSecondQuantization.modes_left_subset_closure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:22:02.692021+00:00
-- url     : https://prove2.me/theorems/9406b9b7-a43e-4a94-a307-dadba5458aa0
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) : modes u ⊆ closureModes col u v
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.modes_left_subset_closure` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.modes_left_subset_closure
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.modes_left_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    modes u ⊆ closureModes col u v := by sorry
