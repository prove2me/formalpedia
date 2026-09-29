-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffHashimoto_coreOp_id
-- name    : BookProof.NavierStokesFlow.DiffHashimoto.coreOp_id
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:50:54.43026+00:00
-- url     : https://prove2.me/theorems/42677652-a149-4d68-bd9e-b976587155f5
-- title:
--   The Lean 4 theorem `coreOp_id` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreOp_id` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffHashimoto.lean

-- Generated from ChapterNavierStokesDiffHashimoto.lean — theorem BookProof.NavierStokesFlow.DiffHashimoto.coreOp_id
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

theorem BookProof.NavierStokesFlow.DiffHashimoto.coreOp_id {d : ℕ} :
    coreOp (LinearMap.id (R := ℂ) (M := MvPolynomial (Fin d) ℂ))
      = LinearMap.id (R := ℂ) (M := (polyGaussCore (d := d))) := by sorry
