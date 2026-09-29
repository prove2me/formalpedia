-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_harmonicOsc_add_linearPotential_essentiallySelfAdjoint
-- name    : BookProof.HermiteRelative.harmonicOsc_add_linearPotential_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:20:47.469139+00:00
-- url     : https://prove2.me/theorems/2e9bb604-55b2-4a92-ad12-b9e0c25a8bd7
-- title:
--   The Lean 4 theorem `harmonicOsc_add_linearPotential_essentiallySelfAdjoint` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `harmonicOsc_add_linearPotential_essentiallySelfAdjoint` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.harmonicOsc_add_linearPotential_essentiallySelfAdjoint
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

theorem BookProof.HermiteRelative.harmonicOsc_add_linearPotential_essentiallySelfAdjoint (b : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (quadOp (fun _ => (1 : ℝ)) + foOp b 0) := by sorry
