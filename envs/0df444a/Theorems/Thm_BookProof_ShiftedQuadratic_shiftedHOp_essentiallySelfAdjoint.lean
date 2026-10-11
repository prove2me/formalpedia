-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_essentiallySelfAdjoint
-- name    : BookProof.ShiftedQuadratic.shiftedHOp_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:27:48.356414+00:00
-- url     : https://prove2.me/theorems/8254f2c7-242b-4106-b8dd-dbbd5c6466f8
-- title:
--   `BookProof.ShiftedQuadratic.shiftedHOp_essentiallySelfAdjoint` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) : EssentiallySelfAdjointOn (polyGaussCoreT (shiftVec c b) (boostVec c b')) (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.shiftedHOp_essentiallySelfAdjoint` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) : EssentiallySelfAdjointOn (polyGaussCoreT (shiftVec c b) (boostVec c b')) (shiftedHOp (shiftVec c b) (boostVec c b') c b b')
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.shiftedHOp_essentiallySelfAdjoint`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.shiftedHOp_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
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

theorem BookProof.ShiftedQuadratic.shiftedHOp_essentiallySelfAdjoint (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) :
    EssentiallySelfAdjointOn (polyGaussCoreT (shiftVec c b) (boostVec c b'))
      (shiftedHOp (shiftVec c b) (boostVec c b') c b b') := by sorry
