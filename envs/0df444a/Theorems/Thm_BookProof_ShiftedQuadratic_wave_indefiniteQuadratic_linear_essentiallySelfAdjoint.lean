-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_wave_indefiniteQuadratic_linear_essentiallySelfAdjoint
-- name    : BookProof.ShiftedQuadratic.wave_indefiniteQuadratic_linear_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:44:48.351979+00:00
-- url     : https://prove2.me/theorems/c36c9b42-fc78-428d-9796-196afb5d13cc
-- title:
--   `BookProof.ShiftedQuadratic.wave_indefiniteQuadratic_linear_essentiallySelfAdjoint` (n : ℕ) (b b' : Fin (1 + n) → ℝ) : EssentiallySelfAdjointOn (polyGaussCoreT (shiftVec (minkowski
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.wave_indefiniteQuadratic_linear_essentiallySelfAdjoint` (n : ℕ) (b b' : Fin (1 + n) → ℝ) : EssentiallySelfAdjointOn (polyGaussCoreT (shiftVec (minkowskiCoeff n) b) (boostVec (minkowskiCoeff n) b')) (shiftedHOp (shiftVec (minkowskiCoeff n) b) (boostVec (minkowskiCoeff n) b') (minkowskiCoeff n) b b')
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.wave_indefiniteQuadratic_linear_essentiallySelfAdjoint`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.wave_indefiniteQuadratic_linear_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadratic.wave_indefiniteQuadratic_linear_essentiallySelfAdjoint (n : ℕ)
    (b b' : Fin (1 + n) → ℝ) :
    EssentiallySelfAdjointOn
      (polyGaussCoreT (shiftVec (minkowskiCoeff n) b) (boostVec (minkowskiCoeff n) b'))
      (shiftedHOp (shiftVec (minkowskiCoeff n) b) (boostVec (minkowskiCoeff n) b')
        (minkowskiCoeff n) b b') := by sorry
