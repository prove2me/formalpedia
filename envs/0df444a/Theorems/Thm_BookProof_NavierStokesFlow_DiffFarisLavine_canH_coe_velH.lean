-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_canH_coe_velH
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.canH_coe_velH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:38:34.834375+00:00
-- url     : https://prove2.me/theorems/94ad4f52-b037-4fa5-b483-ffb615714129
-- title:
--   (x : lpFiniteModes Vel) : ((canH A c x : lpFiniteModes Vel) : L2I Vel) = velH A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.canH_coe_velH` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.canH_coe_velH
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.canH_coe_velH (x : lpFiniteModes Vel) :
    ((canH A c x : lpFiniteModes Vel) : L2I Vel)
      = velH A c (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x) := by sorry
