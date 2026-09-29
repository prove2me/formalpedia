-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_diffMaxH_symmetricOn
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:04:23.073281+00:00
-- url     : https://prove2.me/theorems/f7bb9f10-9801-43e0-9952-4fcfa273a5ca
-- title:
--   : SymmetricOn (diffMaxDom (velMu A (seqConst c))) (diffMaxH A c)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_symmetricOn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_symmetricOn
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_symmetricOn :
    SymmetricOn (diffMaxDom (velMu A (seqConst c))) (diffMaxH A c) := by sorry
