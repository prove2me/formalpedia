-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_diffMaxN_add_one_surjective
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_add_one_surjective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:16:51.521064+00:00
-- url     : https://prove2.me/theorems/ab8259d0-0f5d-4adf-80aa-f28988061530
-- title:
--   (mu : ℝ) (hmu : 0 ≤ mu) (f : L2d 3) : ∃ z : diffMaxDom mu, diffMaxN mu z + (z : L2d 3) = f
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_add_one_surjective` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_add_one_surjective
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxN_add_one_surjective (mu : ℝ) (hmu : 0 ≤ mu) (f : L2d 3) :
    ∃ z : diffMaxDom mu, diffMaxN mu z + (z : L2d 3) = f := by sorry
