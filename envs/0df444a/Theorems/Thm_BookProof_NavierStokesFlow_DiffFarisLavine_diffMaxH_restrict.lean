-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_diffMaxH_restrict
-- name    : BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_restrict
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T10:02:58.255524+00:00
-- url     : https://prove2.me/theorems/7ef9b705-12b8-42a4-8b18-a070ae9575c2
-- title:
--   The Lean 4 theorem `diffMaxH_restrict` in the `ChapterNavierStokesDiffFarisLavine` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `diffMaxH_restrict` in the `ChapterNavierStokesDiffFarisLavine` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffFarisLavine.lean

-- Generated from ChapterNavierStokesDiffFarisLavine.lean — theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_restrict
import Mathlib
import Definitions.Def_ChapterNavierStokesDiffFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Theorems.Thm_BookProof_NavierStokesFlow_DiffFarisLavine_polyGaussCore_le_diffMaxDom
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

theorem BookProof.NavierStokesFlow.DiffFarisLavine.diffMaxH_restrict :
    (diffMaxH A c).comp
        (Submodule.inclusion (polyGaussCore_le_diffMaxDom (velMu A (seqConst c))))
      = (polyGaussCore (d := 3)).subtype.comp (nsDiffH A c) := by sorry
