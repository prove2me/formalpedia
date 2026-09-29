-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_sum_hEx_vEx
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.sum_hEx_vEx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:26:10.900028+00:00
-- url     : https://prove2.me/theorems/01744730-b90f-4ada-8f84-2e18920b94af
-- title:
--   : (hEx 0 + hEx 1) vEx = (2 : ℂ) • EuclideanSpace.single (0 : Fin 2) (1 : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.sum_hEx_vEx` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.sum_hEx_vEx
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.sum_hEx_vEx :
    (hEx 0 + hEx 1) vEx = (2 : ℂ) • EuclideanSpace.single (0 : Fin 2) (1 : ℂ) := by sorry
