-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_coreOp_sum
-- name    : BookProof.HermiteRelative.coreOp_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:10:02.842312+00:00
-- url     : https://prove2.me/theorems/d4398a16-ce4e-4614-9db6-9ba22df418ea
-- title:
--   The Lean 4 theorem `coreOp_sum` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreOp_sum` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.coreOp_sum
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

theorem BookProof.HermiteRelative.coreOp_sum {ι : Type*} (s : Finset ι)
    (T : ι → MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    coreOp (∑ i ∈ s, T i) = ∑ i ∈ s, coreOp (T i) := by sorry
