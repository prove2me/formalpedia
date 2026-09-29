-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_modes_right_subset_closure
-- name    : BookProof.FockSecondQuantization.modes_right_subset_closure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:22:45.498834+00:00
-- url     : https://prove2.me/theorems/eeae200b-df2e-4dd7-97e1-b06d1970ba9a
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) : modes v ⊆ closureModes col u v
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.modes_right_subset_closure` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.modes_right_subset_closure
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.modes_right_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    modes v ⊆ closureModes col u v := by sorry
