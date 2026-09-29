-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockComparison_domain_ne_top
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockComparison_domain_ne_top
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:08:33.586531+00:00
-- url     : https://prove2.me/theorems/ad059e35-662f-431e-8a63-1cd6c059f14f
-- title:
--   : (fockCore fiberCore : Submodule ℂ (lp fiberSector 2)) ≠ ⊤
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockComparison_domain_ne_top` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockFarisLavine.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockComparison_domain_ne_top
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

theorem BookProof.NavierStokesFlow.SecondQuant.fockComparison_domain_ne_top :
    (fockCore fiberCore : Submodule ℂ (lp fiberSector 2)) ≠ ⊤ := by sorry
