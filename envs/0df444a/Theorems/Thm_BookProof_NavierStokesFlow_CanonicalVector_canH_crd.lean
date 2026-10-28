-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_CanonicalVector_canH_crd
-- name    : BookProof.NavierStokesFlow.CanonicalVector.canH_crd
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T03:23:43.87968+00:00
-- url     : https://prove2.me/theorems/14b797f6-cbe5-4491-94d1-2d47bfd13d89
-- title:
--   canH_crd
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.CanonicalVector.canH_crd` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesCanonicalVector.lean`).
-- source:
--   https://github.com/leonardpedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesCanonicalVector.lean

-- Generated from ChapterNavierStokesCanonicalVector.lean — theorem BookProof.NavierStokesFlow.CanonicalVector.canH_crd
import Mathlib
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.CanonicalVector


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

theorem BookProof.NavierStokesFlow.CanonicalVector.canH_crd (x : lpFiniteModes Vel) (γ : Vel) :
    crd (canH A c x) γ = canFun A c (crd x) γ := by sorry
