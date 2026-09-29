-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_ofSectors_apply
-- name    : BookProof.NavierStokesFlow.SecondQuant.ofSectors_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:59:59.448796+00:00
-- url     : https://prove2.me/theorems/6dc7259a-24ba-425b-8d07-518bf23f1e9a
-- title:
--   (g : ∀ m, S m) (h : (Function.support fun m => ‖g m‖).Finite) (m : ι) : (ofSectors g h : ∀ m, S m) m = g m
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.ofSectors_apply` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSecondQuant.lean — theorem BookProof.NavierStokesFlow.SecondQuant.ofSectors_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesSecondQuant
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant









open scoped ENNReal



variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]

theorem BookProof.NavierStokesFlow.SecondQuant.ofSectors_apply (g : ∀ m, S m) (h : (Function.support fun m => ‖g m‖).Finite)
    (m : ι) : (ofSectors g h : ∀ m, S m) m = g m := by sorry
