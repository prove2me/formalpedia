-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_nsDiffN_eq_ladder
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_eq_ladder
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:19:29.23159+00:00
-- url     : https://prove2.me/theorems/5b7fe266-0477-4c5a-802d-a9ec7d5f2b67
-- title:
--   (mu : ℝ) : nsDiffN mu = (((2 * mu : ℝ) : ℂ)) • (∑ i, (creOp i).comp (annOp i)) + (((3 * mu + 1 : ℝ) : ℂ)) • LinearMap.id
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_eq_ladder` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_eq_ladder
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_eq_ladder (mu : ℝ) :
    nsDiffN mu = (((2 * mu : ℝ) : ℂ)) • (∑ i, (creOp i).comp (annOp i))
      + (((3 * mu + 1 : ℝ) : ℂ)) • LinearMap.id := by sorry
