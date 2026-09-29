-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockOp_ge_norm_sq
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockOp_ge_norm_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:53:00.589838+00:00
-- url     : https://prove2.me/theorems/a4158f30-acc6-4ea2-b08c-6154b689d2be
-- title:
--   (N : ∀ m, D m →ₗ[ℂ] D m) (hb : ∀ (m : ι) (x : D m), ‖(x : S m)‖ ^ 2 ≤ (inner ℂ ((x : S m)) ((N m x : D m) : S m) : ℂ).re) (v : fockCore D) : ‖(v : lp S 2)‖ ^ 2 ≤...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockOp_ge_norm_sq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockFarisLavine.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_ge_norm_sq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant








open scoped ENNReal



open FarisLavineLift

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}

theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_ge_norm_sq (N : ∀ m, D m →ₗ[ℂ] D m)
    (hb : ∀ (m : ι) (x : D m),
      ‖(x : S m)‖ ^ 2 ≤ (inner ℂ ((x : S m)) ((N m x : D m) : S m) : ℂ).re)
    (v : fockCore D) :
    ‖(v : lp S 2)‖ ^ 2
      ≤ (inner ℂ ((v : lp S 2)) ((fockOp N v : fockCore D) : lp S 2) : ℂ).re := by sorry
