-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_crd_numSeq
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.crd_numSeq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:39:24.921127+00:00
-- url     : https://prove2.me/theorems/7790d09e-1e7b-4512-8fe4-284fe4fb2929
-- title:
--   (i : Fin 3) (x : lpFiniteModes Vel) (β : Vel) : crd (numSeq i x) β = ((β i : ℝ) : ℂ) * crd x β
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.crd_numSeq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.crd_numSeq
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.crd_numSeq (i : Fin 3) (x : lpFiniteModes Vel) (β : Vel) :
    crd (numSeq i x) β = ((β i : ℝ) : ℂ) * crd x β := by sorry
