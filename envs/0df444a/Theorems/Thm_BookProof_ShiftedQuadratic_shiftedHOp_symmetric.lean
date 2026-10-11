-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_symmetric
-- name    : BookProof.ShiftedQuadratic.shiftedHOp_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:26:58.224233+00:00
-- url     : https://prove2.me/theorems/a6318a09-aa53-4b51-b671-c83d3c3c2957
-- title:
--   `BookProof.ShiftedQuadratic.shiftedHOp_symmetric` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) : SymmetricOn (polyGaussCoreT (shiftVec c b) (boostVec c b')) (shiftedHOp (shiftVec c b)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.shiftedHOp_symmetric` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) : SymmetricOn (polyGaussCoreT (shiftVec c b) (boostVec c b')) (shiftedHOp (shiftVec c b) (boostVec c b') c b b')
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.shiftedHOp_symmetric`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.shiftedHOp_symmetric
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

theorem BookProof.ShiftedQuadratic.shiftedHOp_symmetric (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) :
    SymmetricOn (polyGaussCoreT (shiftVec c b) (boostVec c b'))
      (shiftedHOp (shiftVec c b) (boostVec c b') c b b') := by sorry
