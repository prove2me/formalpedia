-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_diffMaxH_relative_bound
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_relative_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:16:00.834454+00:00
-- url     : https://prove2.me/theorems/8c9c70b5-c3ab-4b55-a9dc-dd2577d7e4aa
-- title:
--   : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ z : diffMaxDom (velMu A (seqConst c)), ‖diffMaxH A c z‖ ^ 2 ≤ a * ‖diffMaxN (velMu A (seqConst c)) z‖ ^ 2 + b * ‖(z : L2d 3)‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_relative_bound` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_relative_bound
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_relative_bound :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ z : diffMaxDom (velMu A (seqConst c)),
      ‖diffMaxH A c z‖ ^ 2
        ≤ a * ‖diffMaxN (velMu A (seqConst c)) z‖ ^ 2 + b * ‖(z : L2d 3)‖ ^ 2 := by sorry
