-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_quadForm_nsDiffN_embedCore
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.quadForm_nsDiffN_embedCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:16:18.02598+00:00
-- url     : https://prove2.me/theorems/d968add3-9b6e-47fb-b5b9-fdd1d04a0587
-- title:
--   (mu : ℝ) (x : lpFiniteModes Vel) : quadForm ((polyGaussCore (d
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.quadForm_nsDiffN_embedCore` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.quadForm_nsDiffN_embedCore
import Mathlib
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiffFarisLavine













open MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato

noncomputable section

















variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.

theorem BookProof.NavierStokesFlow.DiffFarisLavine.quadForm_nsDiffN_embedCore (mu : ℝ) (x : lpFiniteModes Vel) :
    quadForm ((polyGaussCore (d := 3)).subtype.comp (nsDiffN mu)) (embedCore x)
      = quadForm (diagMax (velSym mu))
          (Submodule.inclusion (finiteModes_le_maxDom (velSym mu)) x) := by sorry
