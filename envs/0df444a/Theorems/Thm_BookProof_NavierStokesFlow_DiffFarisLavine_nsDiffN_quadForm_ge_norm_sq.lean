-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_nsDiffN_quadForm_ge_norm_sq
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_quadForm_ge_norm_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:21:58.920118+00:00
-- url     : https://prove2.me/theorems/79798872-1b80-4237-98cf-acd91ed5ee81
-- title:
--   (mu : ℝ) (hmu : 0 ≤ mu) (f : polyGaussCore (d
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_quadForm_ge_norm_sq` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_quadForm_ge_norm_sq
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_quadForm_ge_norm_sq (mu : ℝ) (hmu : 0 ≤ mu) (f : polyGaussCore (d := 3)) :
    ‖(f : L2d 3)‖ ^ 2
      ≤ quadForm ((polyGaussCore (d := 3)).subtype.comp (nsDiffN mu)) f := by sorry
