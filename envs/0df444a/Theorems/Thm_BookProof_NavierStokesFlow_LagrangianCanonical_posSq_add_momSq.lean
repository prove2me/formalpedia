-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_posSq_add_momSq
-- name    : BookProof.NavierStokesFlow.LagrangianCanonical.posSq_add_momSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:35:02.051088+00:00
-- url     : https://prove2.me/theorems/2b17bfbd-207f-4c06-967d-0de5686b3270
-- title:
--   (i : Fin 3) : (pos i).comp (pos i) + (mom i).comp (mom i) = (2 : ℂ) • numOp i + LinearMap.id
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.LagrangianCanonical.posSq_add_momSq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.posSq_add_momSq
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent

theorem BookProof.NavierStokesFlow.LagrangianCanonical.posSq_add_momSq (i : Fin 3) :
    (pos i).comp (pos i) + (mom i).comp (mom i)
      = (2 : ℂ) • numOp i + LinearMap.id := by sorry
