-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_not_bounded
-- name    : BookProof.ShiftedQuadratic.shiftedHOp_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:43:04.824901+00:00
-- url     : https://prove2.me/theorems/ecd24704-7a89-4778-8235-94fb97c4403c
-- title:
--   `BookProof.ShiftedQuadratic.shiftedHOp_not_bounded` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) {i : Fin d} : ¬ ∃ C : ℝ, ∀ f : polyGaussCoreT (shiftVec c b) (boostVec c b'), ‖shiftedH
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.shiftedHOp_not_bounded` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) {i : Fin d} : ¬ ∃ C : ℝ, ∀ f : polyGaussCoreT (shiftVec c b) (boostVec c b'), ‖shiftedHOp (shiftVec c b) (boostVec c b') c b b' f‖ ≤ C * ‖(f : L2d d)‖
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.shiftedHOp_not_bounded`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.shiftedHOp_not_bounded
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
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

theorem BookProof.ShiftedQuadratic.shiftedHOp_not_bounded (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) {i : Fin d} :
    ¬ ∃ C : ℝ, ∀ f : polyGaussCoreT (shiftVec c b) (boostVec c b'),
        ‖shiftedHOp (shiftVec c b) (boostVec c b') c b b' f‖ ≤ C * ‖(f : L2d d)‖ := by sorry
