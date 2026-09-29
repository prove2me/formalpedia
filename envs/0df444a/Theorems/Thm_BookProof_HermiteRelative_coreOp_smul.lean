-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_coreOp_smul
-- name    : BookProof.HermiteRelative.coreOp_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:49:05.077613+00:00
-- url     : https://prove2.me/theorems/a02b61a4-aca1-4647-b8f2-e0d1de6e6c31
-- title:
--   The Lean 4 theorem `coreOp_smul` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreOp_smul` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.coreOp_smul
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
open BookProof.HermiteRelative









open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}





variable {d : ℕ}

theorem BookProof.HermiteRelative.coreOp_smul (r : ℂ) (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    coreOp (r • T) = r • coreOp T := by sorry
