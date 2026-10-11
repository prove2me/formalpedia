-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_equilibrium_orthogonal_to_kernel
-- name    : BookProof.ShiftedQuadraticDegenerate.equilibrium_orthogonal_to_kernel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T22:59:13.901929+00:00
-- url     : https://prove2.me/theorems/d5bc4449-acc1-4141-b269-9a41216d80a5
-- title:
--   `BookProof.ShiftedQuadraticDegenerate.equilibrium_orthogonal_to_kernel` {A : Matrix (Fin d) (Fin d) ℝ} (hsym : ∀ i j, A i j = A j i) {a w : Fin d → ℝ} (ha : ∀ i, ∑ j, A i j * a j =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticDegenerate`.
--
--   `BookProof.ShiftedQuadraticDegenerate.equilibrium_orthogonal_to_kernel` {A : Matrix (Fin d) (Fin d) ℝ} (hsym : ∀ i j, A i j = A j i) {a w : Fin d → ℝ} (ha : ∀ i, ∑ j, A i j * a j = w i) {v : Fin d → ℝ} (hv : ∀ i, ∑ j, A i j * v j = 0) : ∑ i, w i * v i = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticDegenerate.equilibrium_orthogonal_to_kernel`.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — theorem BookProof.ShiftedQuadraticDegenerate.equilibrium_orthogonal_to_kernel
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
open BookProof.ShiftedQuadraticDegenerate



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.ShiftedQuadraticMatrix
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.StoneEigenflow

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadraticDegenerate.equilibrium_orthogonal_to_kernel {A : Matrix (Fin d) (Fin d) ℝ}
    (hsym : ∀ i j, A i j = A j i) {a w : Fin d → ℝ} (ha : ∀ i, ∑ j, A i j * a j = w i)
    {v : Fin d → ℝ} (hv : ∀ i, ∑ j, A i j * v j = 0) :
    ∑ i, w i * v i = 0 := by sorry
