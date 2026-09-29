-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffHashimoto_nsDiffH_symmetricOn
-- name    : BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:55.449969+00:00
-- url     : https://prove2.me/theorems/b67459af-c1fc-49a2-973c-f48fa8cb8990
-- title:
--   The Lean 4 theorem `nsDiffH_symmetricOn` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsDiffH_symmetricOn` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffHashimoto.lean

-- Generated from ChapterNavierStokesDiffHashimoto.lean — theorem BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_symmetricOn
import Mathlib
import Definitions.Def_ChapterNavierStokesDiffHashimoto
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.DiffHashimoto







open Filter Topology



open MvPolynomial
open BookProof.FarisLavine BookProof.HashimotoShiftInvert BookProof.EsaClosure
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteRelative
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 4000000 in
-- The core operators unfold through several linear equivalences on a submodule of `L²(ℝ³)`,
-- so the default heartbeat budget is not enough.

theorem BookProof.NavierStokesFlow.DiffHashimoto.nsDiffH_symmetricOn :
    SymmetricOn (polyGaussCore (d := 3))
      ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) := by sorry
