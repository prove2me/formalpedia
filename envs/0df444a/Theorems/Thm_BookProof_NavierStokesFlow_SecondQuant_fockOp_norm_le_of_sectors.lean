-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockOp_norm_le_of_sectors
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_le_of_sectors
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:53:09.697627+00:00
-- url     : https://prove2.me/theorems/bff32cbe-db46-472d-9c2f-89dbcbf3b82d
-- title:
--   (H N : ∀ m, D m →ₗ[ℂ] D m) (cst : ℝ) (hc : 0 ≤ cst) (hb : ∀ (m : ι) (x : D m), ‖((H m x : D m) : S m)‖ ≤ cst * ‖((N m x : D m) : S m)‖) (v : fockCore D) : ‖((fockOp H v...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_le_of_sectors` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockFarisLavine.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_le_of_sectors
import Mathlib
import Definitions.Def_ChapterNavierStokesFockFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant








open scoped ENNReal



open FarisLavineLift

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}

theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_le_of_sectors (H N : ∀ m, D m →ₗ[ℂ] D m) (cst : ℝ) (hc : 0 ≤ cst)
    (hb : ∀ (m : ι) (x : D m), ‖((H m x : D m) : S m)‖ ≤ cst * ‖((N m x : D m) : S m)‖)
    (v : fockCore D) :
    ‖((fockOp H v : fockCore D) : lp S 2)‖ ≤ cst * ‖((fockOp N v : fockCore D) : lp S 2)‖ := by sorry
