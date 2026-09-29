-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_oscPoly_eq
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.oscPoly_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:45:39.287328+00:00
-- url     : https://prove2.me/theorems/18f46bb6-e3eb-481f-98ce-1e06a0546ae7
-- title:
--   (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) : momPoly i (momPoly i p) + mulXPoly i (mulXPoly i (((1 / 4 : ℂ)) • p)) = crePoly i (annPoly i p) + ((1 / 2 : ℂ)) • p
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.oscPoly_eq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.oscPoly_eq
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.oscPoly_eq (i : Fin 3) (p : MvPolynomial (Fin 3) ℂ) :
    momPoly i (momPoly i p) + mulXPoly i (mulXPoly i (((1 / 4 : ℂ)) • p))
      = crePoly i (annPoly i p) + ((1 / 2 : ℂ)) • p := by sorry
