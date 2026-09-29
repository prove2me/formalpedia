-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_norm_sum_sq_eq
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_sq_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:53:10.925706+00:00
-- url     : https://prove2.me/theorems/0eed3482-ccdc-43fc-8ecc-eb58614fc02c
-- title:
--   {κ : Type*} (s : Finset κ) (a : κ → F) : ‖∑ k ∈ s, a k‖ ^ 2 = ∑ k ∈ s, ∑ l ∈ s, (inner ℂ (a k) (a l) : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_sq_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_sq_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_sq_eq {κ : Type*} (s : Finset κ) (a : κ → F) :
    ‖∑ k ∈ s, a k‖ ^ 2 = ∑ k ∈ s, ∑ l ∈ s, (inner ℂ (a k) (a l) : ℂ).re := by sorry
