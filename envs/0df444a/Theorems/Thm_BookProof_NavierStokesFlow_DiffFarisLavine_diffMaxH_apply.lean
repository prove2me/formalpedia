-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_diffMaxH_apply
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:41:24.503609+00:00
-- url     : https://prove2.me/theorems/a5a2a3e4-1864-4b9f-b8c7-246166d7b4ce
-- title:
--   (z : maxDom (velSym (velMu A (seqConst c)))) : diffMaxH A c (diffMaxEquiv (velMu A (seqConst c)) z) = velUnitary ((velH A (seqConst c) z : L2I Vel))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_apply` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_apply
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_apply (z : maxDom (velSym (velMu A (seqConst c)))) :
    diffMaxH A c (diffMaxEquiv (velMu A (seqConst c)) z)
      = velUnitary ((velH A (seqConst c) z : L2I Vel)) := by sorry
