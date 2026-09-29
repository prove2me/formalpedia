-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockComparison_ge_norm_sq
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockComparison_ge_norm_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:10:22.813826+00:00
-- url     : https://prove2.me/theorems/ba634ff9-d10d-4ff3-a271-af60ed0f6cf3
-- title:
--   (d : ℕ) (p q : Fin d → ℕ → ℝ) (v : fockCore fiberCore) : ‖(v : lp fiberSector 2)‖ ^ 2 ≤ (inner ℂ ((v : lp fiberSector 2)) ((fockComparison d p q v : fockCore fiberCore) : lp fiberSector 2) : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockComparison_ge_norm_sq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockFarisLavine.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockComparison_ge_norm_sq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant








open scoped ENNReal



open FarisLavineLift

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}



















open FarisLavineLift LpNat DiagonalEsa

theorem BookProof.NavierStokesFlow.SecondQuant.fockComparison_ge_norm_sq (d : ℕ) (p q : Fin d → ℕ → ℝ) (v : fockCore fiberCore) :
    ‖(v : lp fiberSector 2)‖ ^ 2
      ≤ (inner ℂ ((v : lp fiberSector 2))
          ((fockComparison d p q v : fockCore fiberCore) : lp fiberSector 2) : ℂ).re := by sorry
