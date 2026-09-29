-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_norm_nEx
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.norm_nEx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:52:35.311263+00:00
-- url     : https://prove2.me/theorems/cce3596e-1bca-48ae-a3e6-8d637c17811f
-- title:
--   (k : Fin 2) (x : E2) : ‖nEx k x‖ = ‖x k‖
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.norm_nEx` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_nEx
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_nEx (k : Fin 2) (x : E2) : ‖nEx k x‖ = ‖x k‖ := by sorry
