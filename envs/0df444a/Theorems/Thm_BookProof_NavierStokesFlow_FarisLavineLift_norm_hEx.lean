-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_norm_hEx
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.norm_hEx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:51:12.114385+00:00
-- url     : https://prove2.me/theorems/fb389e1c-4da4-4c0e-affd-b1525d97b757
-- title:
--   (k : Fin 2) (x : E2) : ‖hEx k x‖ = ‖x k‖
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.norm_hEx` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_hEx
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_hEx (k : Fin 2) (x : E2) : ‖hEx k x‖ = ‖x k‖ := by sorry
