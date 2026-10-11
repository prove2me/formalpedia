-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_exists_equilibrium_iff
-- name    : BookProof.ShiftedQuadraticDegenerate.exists_equilibrium_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:25:01.270367+00:00
-- url     : https://prove2.me/theorems/1b4274f7-1b27-4c16-a757-f6a3b6cf58f5
-- title:
--   `BookProof.ShiftedQuadraticDegenerate.exists_equilibrium_iff` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (w : Fin d → ℝ) : (∃ a : Fin d → ℝ, ∀ i, ∑ j, A i j * a j = w i) ↔
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticDegenerate`.
--
--   `BookProof.ShiftedQuadraticDegenerate.exists_equilibrium_iff` {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (w : Fin d → ℝ) : (∃ a : Fin d → ℝ, ∀ i, ∑ j, A i j * a j = w i) ↔ ∀ v : Fin d → ℝ, (∀ i, ∑ j, A i j * v j = 0) → ∑ i, w i * v i = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticDegenerate.exists_equilibrium_iff`.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — theorem BookProof.ShiftedQuadraticDegenerate.exists_equilibrium_iff
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

theorem BookProof.ShiftedQuadraticDegenerate.exists_equilibrium_iff {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (w : Fin d → ℝ) :
    (∃ a : Fin d → ℝ, ∀ i, ∑ j, A i j * a j = w i)
      ↔ ∀ v : Fin d → ℝ, (∀ i, ∑ j, A i j * v j = 0) → ∑ i, w i * v i = 0 := by sorry
