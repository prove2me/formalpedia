-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_one_le_diffMu
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.one_le_diffMu
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:45:02.920946+00:00
-- url     : https://prove2.me/theorems/b4569076-0090-4c54-a148-41e998e4238b
-- title:
--   : 1 ≤ diffMu A c
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.one_le_diffMu` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.one_le_diffMu
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.one_le_diffMu : 1 ≤ diffMu A c := by sorry
