-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_nsDiffH_esa_of_farisLavine
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_esa_of_farisLavine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:45:48.093799+00:00
-- url     : https://prove2.me/theorems/d3ce499c-4e0b-4c30-9329-e2a4d9186027
-- title:
--   : EssentiallySelfAdjointOn (polyGaussCore (d
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_esa_of_farisLavine` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_esa_of_farisLavine
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_esa_of_farisLavine :
    EssentiallySelfAdjointOn (polyGaussCore (d := 3))
      ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) := by sorry
