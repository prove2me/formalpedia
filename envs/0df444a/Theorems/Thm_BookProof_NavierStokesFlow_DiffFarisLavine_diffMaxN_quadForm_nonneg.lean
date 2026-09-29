-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_diffMaxN_quadForm_nonneg
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:18:36.982806+00:00
-- url     : https://prove2.me/theorems/e8502a1c-c6b2-49a9-8293-9ea3fb9ae4e9
-- title:
--   (mu : ℝ) (hmu : 0 ≤ mu) (z : diffMaxDom mu) : 0 ≤ quadForm (diffMaxN mu) z
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_quadForm_nonneg` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_quadForm_nonneg
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_quadForm_nonneg (mu : ℝ) (hmu : 0 ≤ mu) (z : diffMaxDom mu) :
    0 ≤ quadForm (diffMaxN mu) z := by sorry
