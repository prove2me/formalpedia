-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_orthonormal_hermiteTRLp
-- name    : BookProof.ShiftedQuadraticMatrix.orthonormal_hermiteTRLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:52:02.749889+00:00
-- url     : https://prove2.me/theorems/0a680ed9-17be-4acf-89a2-c283e2c3aafe
-- title:
--   `BookProof.ShiftedQuadraticMatrix.orthonormal_hermiteTRLp` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d) : Orthonormal ℂ (hermiteTRLp (d := d) O a k)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.orthonormal_hermiteTRLp` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d) : Orthonormal ℂ (hermiteTRLp (d := d) O a k)
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.orthonormal_hermiteTRLp`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.orthonormal_hermiteTRLp
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
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
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

theorem BookProof.ShiftedQuadraticMatrix.orthonormal_hermiteTRLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (a k : Vd d) : Orthonormal ℂ (hermiteTRLp (d := d) O a k) := by sorry
