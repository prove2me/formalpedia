-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_symmetricOn_of_polySym
-- name    : BookProof.HermiteRelative.symmetricOn_of_polySym
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:50:41.41911+00:00
-- url     : https://prove2.me/theorems/d4927d64-28ba-49ba-bc04-256f8260a50f
-- title:
--   The Lean 4 theorem `symmetricOn_of_polySym` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `symmetricOn_of_polySym` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.symmetricOn_of_polySym
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

set_option maxHeartbeats 1000000 in
-- the `L²` coercions of the Gauss–polynomial core make this defeq check expensive

theorem BookProof.HermiteRelative.symmetricOn_of_polySym {T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ}
    (hT : BookProof.YangMillsHermite.PolySym T) :
    SymmetricOn (polyGaussCore (d := d))
      ((polyGaussCore (d := d)).subtype ∘ₗ coreOp T) := by sorry
