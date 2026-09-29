-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_crd_numOp
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.crd_numOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:44:39.569282+00:00
-- url     : https://prove2.me/theorems/082cc05f-6c00-4bfd-a104-3f123874daf0
-- title:
--   (i : Fin 3) (x : lpFiniteModes Vel) : crd (numOp i x) = fun β => ((β i : ℝ) : ℂ) * crd x β
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.crd_numOp` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.crd_numOp
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent

theorem BookProof.NavierStokesFlow.LagrangianCanonical.crd_numOp (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (numOp i x) = fun β => ((β i : ℝ) : ℂ) * crd x β := by sorry
