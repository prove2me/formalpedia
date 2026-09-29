-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_intertwined_nsDiffN
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.intertwined_nsDiffN
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:46:32.459753+00:00
-- url     : https://prove2.me/theorems/95dd8185-04e0-4205-98c7-b5d0752ba6ef
-- title:
--   (mu : ℝ) : Intertwined (velNcore mu) (nsDiffN mu)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.intertwined_nsDiffN` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.intertwined_nsDiffN
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.intertwined_nsDiffN (mu : ℝ) : Intertwined (velNcore mu) (nsDiffN mu) := by sorry
