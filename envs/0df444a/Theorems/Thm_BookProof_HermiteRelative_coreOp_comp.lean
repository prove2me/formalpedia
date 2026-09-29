-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_coreOp_comp
-- name    : BookProof.HermiteRelative.coreOp_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:48:54.264566+00:00
-- url     : https://prove2.me/theorems/f7fdab07-88b8-4bcf-a16e-fb0fd9be6839
-- title:
--   The Lean 4 theorem `coreOp_comp` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreOp_comp` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.coreOp_comp
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

theorem BookProof.HermiteRelative.coreOp_comp (S T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    coreOp (S.comp T) = (coreOp S).comp (coreOp T) := by sorry
