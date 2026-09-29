-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_velNcore_eq_diagMax
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.velNcore_eq_diagMax
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:03:43.158523+00:00
-- url     : https://prove2.me/theorems/6f41515a-f80b-4a83-99b9-bbb7df83f224
-- title:
--   (mu : ℝ) (x : lpFiniteModes Vel) : ((velNcore mu x : lpFiniteModes Vel) : L2I Vel) = (diagMax (velSym mu) (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) x) : L2I Vel)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.velNcore_eq_diagMax` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.velNcore_eq_diagMax
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.velNcore_eq_diagMax (mu : ℝ) (x : lpFiniteModes Vel) :
    ((velNcore mu x : lpFiniteModes Vel) : L2I Vel)
      = (diagMax (velSym mu)
          (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) x) : L2I Vel) := by sorry
