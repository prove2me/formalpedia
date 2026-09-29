-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_embedCore_surjective
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.embedCore_surjective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:21:14.427346+00:00
-- url     : https://prove2.me/theorems/fb5d7be7-2c35-497f-9784-b63045c642b1
-- title:
--   : Function.Surjective (embedCore)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.embedCore_surjective` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.embedCore_surjective
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.embedCore_surjective : Function.Surjective (embedCore) := by sorry
