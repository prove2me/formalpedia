-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_mulVec_matBoostVec
-- name    : BookProof.ShiftedQuadraticMatrix.mulVec_matBoostVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:46:55.772062+00:00
-- url     : https://prove2.me/theorems/aaddeda0-0272-4788-a457-3f17c7709b94
-- title:
--   `BookProof.ShiftedQuadraticMatrix.mulVec_matBoostVec` {A : Matrix (Fin d) (Fin d) ℝ} (hdet : IsUnit A.det) (b' : Fin d → ℝ) (i : Fin d) : ∑ j, A i j * (matBoostVec A b') j = -(b' i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.mulVec_matBoostVec` {A : Matrix (Fin d) (Fin d) ℝ} (hdet : IsUnit A.det) (b' : Fin d → ℝ) (i : Fin d) : ∑ j, A i j * (matBoostVec A b') j = -(b' i) / 2
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.mulVec_matBoostVec`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.mulVec_matBoostVec
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
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

theorem BookProof.ShiftedQuadraticMatrix.mulVec_matBoostVec {A : Matrix (Fin d) (Fin d) ℝ} (hdet : IsUnit A.det)
    (b' : Fin d → ℝ) (i : Fin d) :
    ∑ j, A i j * (matBoostVec A b') j = -(b' i) / 2 := by sorry
