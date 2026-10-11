-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_hermiteTRLp_mem_coreT
-- name    : BookProof.ShiftedQuadraticMatrix.hermiteTRLp_mem_coreT
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:45:43.477172+00:00
-- url     : https://prove2.me/theorems/df71165d-0a38-4519-b7b3-bb92d6880537
-- title:
--   `BookProof.ShiftedQuadraticMatrix.hermiteTRLp_mem_coreT` (O : Matrix (Fin d) (Fin d) ℝ) (a k : Vd d) (α : Fin d →₀ ℕ) : hermiteTRLp O a k α ∈ polyGaussCoreT a k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.hermiteTRLp_mem_coreT` (O : Matrix (Fin d) (Fin d) ℝ) (a k : Vd d) (α : Fin d →₀ ℕ) : hermiteTRLp O a k α ∈ polyGaussCoreT a k
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.hermiteTRLp_mem_coreT`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.hermiteTRLp_mem_coreT
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
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductBasis
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

theorem BookProof.ShiftedQuadraticMatrix.hermiteTRLp_mem_coreT (O : Matrix (Fin d) (Fin d) ℝ) (a k : Vd d) (α : Fin d →₀ ℕ) :
    hermiteTRLp O a k α ∈ polyGaussCoreT a k := by sorry
