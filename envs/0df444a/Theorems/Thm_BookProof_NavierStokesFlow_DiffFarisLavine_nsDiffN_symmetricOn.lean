-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_nsDiffN_symmetricOn
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:16:07.70555+00:00
-- url     : https://prove2.me/theorems/31fbc5a9-5567-4ad4-a0f1-0e67847066e9
-- title:
--   (mu : ℝ) : SymmetricOn (polyGaussCore (d
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_symmetricOn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_symmetricOn
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.nsDiffN_symmetricOn (mu : ℝ) :
    SymmetricOn (polyGaussCore (d := 3))
      ((polyGaussCore (d := 3)).subtype.comp (nsDiffN mu)) := by sorry
