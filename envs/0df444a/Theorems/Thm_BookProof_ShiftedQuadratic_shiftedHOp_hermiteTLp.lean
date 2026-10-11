-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_hermiteTLp
-- name    : BookProof.ShiftedQuadratic.shiftedHOp_hermiteTLp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:26:40.27898+00:00
-- url     : https://prove2.me/theorems/cf5618b3-b48e-41b1-a6ab-20e4777d5a55
-- title:
--   `BookProof.ShiftedQuadratic.shiftedHOp_hermiteTLp` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) (α : Fin d →₀ ℕ) (h : hermiteTLp (shiftVec c b) (boostVec c b') α ∈ polyGaussCoreT (shif
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.shiftedHOp_hermiteTLp` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) (α : Fin d →₀ ℕ) (h : hermiteTLp (shiftVec c b) (boostVec c b') α ∈ polyGaussCoreT (shiftVec c b) (boostVec c b')) : shiftedHOp (shiftVec c b) (boostVec c b') c b b' ⟨_, h⟩ = (((quadSymbol c α + shiftConst c b b' : ℝ)) : ℂ) • hermiteTLp (shiftVec c b) (boostVec c b') α
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.shiftedHOp_hermiteTLp`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.shiftedHOp_hermiteTLp
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductBasis
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

theorem BookProof.ShiftedQuadratic.shiftedHOp_hermiteTLp (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) (α : Fin d →₀ ℕ)
    (h : hermiteTLp (shiftVec c b) (boostVec c b') α
      ∈ polyGaussCoreT (shiftVec c b) (boostVec c b')) :
    shiftedHOp (shiftVec c b) (boostVec c b') c b b' ⟨_, h⟩
      = (((quadSymbol c α + shiftConst c b b' : ℝ)) : ℂ)
          • hermiteTLp (shiftVec c b) (boostVec c b') α := by sorry
