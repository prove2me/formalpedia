-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_coreOp_apply_prime
-- name    : BookProof.HermiteRelative.coreOp_apply_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:49:56.252948+00:00
-- url     : https://prove2.me/theorems/c1b52cf3-8d84-413f-b8bf-78f2e81a0da7
-- title:
--   The Lean 4 theorem `coreOp_apply'` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreOp_apply'` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.coreOp_apply'
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

theorem BookProof.HermiteRelative.coreOp_apply_prime (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (x : polyGaussCore (d := d)) : coreOp T x = coreEquiv (T (coreEquiv.symm x)) := by sorry
