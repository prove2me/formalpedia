-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_nsDiffH_embedCore
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_embedCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:44:15.498783+00:00
-- url     : https://prove2.me/theorems/fc97d60e-d762-4f08-a9a4-7d39481688f6
-- title:
--   (x : lpFiniteModes Vel) : ((nsDiffH A c (embedCore x) : polyGaussCore (d
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_embedCore` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_embedCore
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

















variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.

theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_embedCore (x : lpFiniteModes Vel) :
    ((nsDiffH A c (embedCore x) : polyGaussCore (d := 3)) : L2d 3)
      = velUnitary ((canH A (seqConst c) x : lpFiniteModes Vel) : L2I Vel) := by sorry
