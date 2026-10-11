-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_not_bounded
-- name    : BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:47:26.944989+00:00
-- url     : https://prove2.me/theorems/623447e4-b96e-45a3-93e8-900e0c95c3e5
-- title:
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_not_bounded` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) (i : Fin d) : ¬ ∃ C : ℝ, ∀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_not_bounded` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) (i : Fin d) : ¬ ∃ C : ℝ, ∀ f : polyGaussCoreT (matShiftVec A b) (matBoostVec A b'), ‖shiftedHMatOp (matShiftVec A b) (matBoostVec A b') A b b' f‖ ≤ C * ‖(f : L2d d)‖
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_not_bounded`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_not_bounded
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadraticMatrix



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_not_bounded {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.IsHermitian) (hdet : IsUnit A.det) (b b' : Fin d → ℝ) (i : Fin d) :
    ¬ ∃ C : ℝ, ∀ f : polyGaussCoreT (matShiftVec A b) (matBoostVec A b'),
        ‖shiftedHMatOp (matShiftVec A b) (matBoostVec A b') A b b' f‖
          ≤ C * ‖(f : L2d d)‖ := by sorry
