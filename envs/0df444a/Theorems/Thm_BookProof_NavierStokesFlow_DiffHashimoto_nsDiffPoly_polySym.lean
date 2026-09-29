-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffHashimoto_nsDiffPoly_polySym
-- name    : BookProof.NavierStokesFlow.DiffHashimoto.nsDiffPoly_polySym
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:18:34.361289+00:00
-- url     : https://prove2.me/theorems/990545f1-1526-4151-84f8-a7d3b4b63122
-- title:
--   The Lean 4 theorem `nsDiffPoly_polySym` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsDiffPoly_polySym` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffHashimoto.lean

-- Generated from ChapterNavierStokesDiffHashimoto.lean — theorem BookProof.NavierStokesFlow.DiffHashimoto.nsDiffPoly_polySym
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

theorem BookProof.NavierStokesFlow.DiffHashimoto.nsDiffPoly_polySym : BookProof.YangMillsHermite.PolySym (nsDiffPoly A c) := by sorry
