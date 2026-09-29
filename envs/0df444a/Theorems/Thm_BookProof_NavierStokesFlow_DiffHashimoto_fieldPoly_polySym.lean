-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DiffHashimoto_fieldPoly_polySym
-- name    : BookProof.NavierStokesFlow.DiffHashimoto.fieldPoly_polySym
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:10:38.33989+00:00
-- url     : https://prove2.me/theorems/11708851-27bf-4fcb-baa2-862e679b2988
-- title:
--   The Lean 4 theorem `fieldPoly_polySym` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fieldPoly_polySym` in the `ChapterNavierStokesDiffHashimoto` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDiffHashimoto.lean

-- Generated from ChapterNavierStokesDiffHashimoto.lean — theorem BookProof.NavierStokesFlow.DiffHashimoto.fieldPoly_polySym
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

theorem BookProof.NavierStokesFlow.DiffHashimoto.fieldPoly_polySym (i : Fin 3) :
    BookProof.YangMillsHermite.PolySym (fieldPoly A c i) := by sorry
