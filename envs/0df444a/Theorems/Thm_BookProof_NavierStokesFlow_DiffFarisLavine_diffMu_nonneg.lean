-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_diffMu_nonneg
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.diffMu_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:42:56.830479+00:00
-- url     : https://prove2.me/theorems/9d568cb2-bbe6-4326-a0ab-d7a146f78baa
-- title:
--   : 0 ≤ diffMu A c
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.diffMu_nonneg` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMu_nonneg
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMu_nonneg : 0 ≤ diffMu A c := by sorry
