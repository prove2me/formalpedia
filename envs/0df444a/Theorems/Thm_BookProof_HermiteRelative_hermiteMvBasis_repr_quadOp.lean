-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_hermiteMvBasis_repr_quadOp
-- name    : BookProof.HermiteRelative.hermiteMvBasis_repr_quadOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:49:19.769985+00:00
-- url     : https://prove2.me/theorems/78afcf4c-c4d9-410f-ba09-2b3f4b322e7a
-- title:
--   The Lean 4 theorem `hermiteMvBasis_repr_quadOp` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteMvBasis_repr_quadOp` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.hermiteMvBasis_repr_quadOp
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

theorem BookProof.HermiteRelative.hermiteMvBasis_repr_quadOp (c : Fin d → ℝ) (u : polyGaussCore (d := d))
    (a : Fin d →₀ ℕ) :
    hermiteMvBasis.repr (quadOp c u) a
      = ((quadSymbol c a : ℝ) : ℂ) * hermiteMvBasis.repr (u : L2d d) a := by sorry
