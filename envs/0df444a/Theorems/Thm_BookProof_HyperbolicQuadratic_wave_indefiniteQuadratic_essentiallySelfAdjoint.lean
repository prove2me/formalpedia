-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_wave_indefiniteQuadratic_essentiallySelfAdjoint
-- name    : BookProof.HyperbolicQuadratic.wave_indefiniteQuadratic_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:24:34.311451+00:00
-- url     : https://prove2.me/theorems/bfbdf010-febb-4f91-be4b-a36f1c4b0623
-- title:
--   The Lean 4 theorem `wave_indefiniteQuadratic_essentiallySelfAdjoint` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `wave_indefiniteQuadratic_essentiallySelfAdjoint` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.wave_indefiniteQuadratic_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

theorem BookProof.HyperbolicQuadratic.wave_indefiniteQuadratic_essentiallySelfAdjoint (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 1 + n)) (quadOp (minkowskiCoeff n)) := by sorry
