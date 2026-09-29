-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_commForm_embedCore
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.commForm_embedCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:15:44.280984+00:00
-- url     : https://prove2.me/theorems/081351f1-dba9-41b1-a2c6-7324a0f9a193
-- title:
--   (x : lpFiniteModes Vel) : commForm ((polyGaussCore (d
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.DiffFarisLavine.commForm_embedCore` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.commForm_embedCore
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.commForm_embedCore (x : lpFiniteModes Vel) :
    commForm ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c))
        ((polyGaussCore (d := 3)).subtype.comp (nsDiffN (velMu A (seqConst c)))) (embedCore x)
      = commForm (velH A (seqConst c)) (diagMax (velSym (velMu A (seqConst c))))
          (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A (seqConst c)))) x) := by sorry
