-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_CanonicalVector_canFun_eq_ladFun
-- name    : BookProof.NavierStokesFlow.CanonicalVector.canFun_eq_ladFun
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T03:23:55.54198+00:00
-- url     : https://prove2.me/theorems/e8bc6d2d-782b-4539-8371-efa51460e409
-- title:
--   canFun_eq_ladFun
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.CanonicalVector.canFun_eq_ladFun` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesCanonicalVector.lean`).
-- source:
--   https://github.com/leonardpedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesCanonicalVector.lean

-- Generated from ChapterNavierStokesCanonicalVector.lean — theorem BookProof.NavierStokesFlow.CanonicalVector.canFun_eq_ladFun
import Mathlib
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.CanonicalVector


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.CanonicalVector.canFun_eq_ladFun (X : Vel → ℂ) (γ : Vel) :
    canFun A c X γ = ladFun A c X γ := by sorry
