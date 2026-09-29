-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_sum_nEx_vEx
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.sum_nEx_vEx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:53:46.792968+00:00
-- url     : https://prove2.me/theorems/1eed9bc3-e188-4f1d-89fc-2ae4608eee10
-- title:
--   : (nEx 0 + nEx 1) vEx = vEx
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.sum_nEx_vEx` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.sum_nEx_vEx
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.sum_nEx_vEx : (nEx 0 + nEx 1) vEx = vEx := by sorry
