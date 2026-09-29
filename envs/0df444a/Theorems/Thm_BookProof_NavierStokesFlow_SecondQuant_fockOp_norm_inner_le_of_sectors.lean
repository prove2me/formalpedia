-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockOp_norm_inner_le_of_sectors
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_inner_le_of_sectors
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:53:03.712713+00:00
-- url     : https://prove2.me/theorems/a15e266a-d2b0-4412-9390-b583106eb5da
-- title:
--   (A N : ∀ m, D m →ₗ[ℂ] D m) (c₂ : ℝ) (hb : ∀ (m : ι) (x : D m), ‖(inner ℂ ((x : S m)) ((A m x : D m) : S m) : ℂ)‖ ≤ c₂ * (inner ℂ ((x : S m)) ((N m x : D m) : S m) :...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_inner_le_of_sectors` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockFarisLavine.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_inner_le_of_sectors
import Mathlib
import Definitions.Def_ChapterNavierStokesFockFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant








open scoped ENNReal



open FarisLavineLift

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}

theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_inner_le_of_sectors (A N : ∀ m, D m →ₗ[ℂ] D m) (c₂ : ℝ)
    (hb : ∀ (m : ι) (x : D m), ‖(inner ℂ ((x : S m)) ((A m x : D m) : S m) : ℂ)‖
      ≤ c₂ * (inner ℂ ((x : S m)) ((N m x : D m) : S m) : ℂ).re)
    (v : fockCore D) :
    ‖(inner ℂ ((v : lp S 2)) ((fockOp A v : fockCore D) : lp S 2) : ℂ)‖
      ≤ c₂ * (inner ℂ ((v : lp S 2)) ((fockOp N v : fockCore D) : lp S 2) : ℂ).re := by sorry
