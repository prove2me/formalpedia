-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_diffMaxN_core_approx
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_core_approx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:17:42.210296+00:00
-- url     : https://prove2.me/theorems/84b9e5c9-af9a-4dc4-a8fd-8aa86b5a907d
-- title:
--   (mu : ℝ) (z : diffMaxDom mu) (ε : ℝ) (hε : 0 < ε) : ∃ y : diffMaxDom mu, (y : L2d 3) ∈ (polyGaussCore (d
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_core_approx` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_core_approx
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_core_approx (mu : ℝ) (z : diffMaxDom mu) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : diffMaxDom mu, (y : L2d 3) ∈ (polyGaussCore (d := 3)) ∧
      ‖(y : L2d 3) - (z : L2d 3)‖ < ε ∧ ‖diffMaxN mu y - diffMaxN mu z‖ < ε := by sorry
