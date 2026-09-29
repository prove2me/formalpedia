-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_oscOp_eq_number
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.oscOp_eq_number
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:22:20.699592+00:00
-- url     : https://prove2.me/theorems/d1d4c878-3b3d-42a6-9d32-be8daca75419
-- title:
--   (i : Fin 3) : oscOp i = (creOp i).comp (annOp i) + ((1 / 2 : ℂ)) • LinearMap.id
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.oscOp_eq_number` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.oscOp_eq_number
import Mathlib
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiffFarisLavine













open MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.

theorem BookProof.NavierStokesFlow.DiffFarisLavine.oscOp_eq_number (i : Fin 3) :
    oscOp i = (creOp i).comp (annOp i) + ((1 / 2 : ℂ)) • LinearMap.id := by sorry
