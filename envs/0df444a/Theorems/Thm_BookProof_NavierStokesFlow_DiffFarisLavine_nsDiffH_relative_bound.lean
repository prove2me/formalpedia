-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_nsDiffH_relative_bound
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_relative_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:16:02.255623+00:00
-- url     : https://prove2.me/theorems/7d09b09c-22c8-4e11-9f61-7606ef7ab924
-- title:
--   : ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ f : polyGaussCore (d
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_relative_bound` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_relative_bound
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffH_relative_bound :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ f : polyGaussCore (d := 3),
      ‖((nsDiffH A c f : polyGaussCore (d := 3)) : L2d 3)‖ ^ 2
        ≤ a * ‖((nsDiffN (diffMu A c) f : polyGaussCore (d := 3)) : L2d 3)‖ ^ 2
          + b * ‖(f : L2d 3)‖ ^ 2 := by sorry
