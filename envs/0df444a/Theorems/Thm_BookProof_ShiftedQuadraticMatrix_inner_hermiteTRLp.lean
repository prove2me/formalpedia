-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_inner_hermiteTRLp
-- name    : BookProof.ShiftedQuadraticMatrix.inner_hermiteTRLp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:45:34.825978+00:00
-- url     : https://prove2.me/theorems/a1ec4a5c-e2bd-4c5d-af14-e221f7a840e2
-- title:
--   `BookProof.ShiftedQuadraticMatrix.inner_hermiteTRLp` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d) (α β : Fin d →₀ ℕ) : (inner ℂ (hermiteTRLp O a k α) (hermiteTRLp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.inner_hermiteTRLp` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d) (α β : Fin d →₀ ℕ) : (inner ℂ (hermiteTRLp O a k α) (hermiteTRLp O a k β) : ℂ) = (inner ℂ (hermiteMvLp (d := d) α) (hermiteMvLp (d := d) β) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.inner_hermiteTRLp`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.inner_hermiteTRLp
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

theorem BookProof.ShiftedQuadraticMatrix.inner_hermiteTRLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (a k : Vd d)
    (α β : Fin d →₀ ℕ) :
    (inner ℂ (hermiteTRLp O a k α) (hermiteTRLp O a k β) : ℂ)
      = (inner ℂ (hermiteMvLp (d := d) α) (hermiteMvLp (d := d) β) : ℂ) := by sorry
