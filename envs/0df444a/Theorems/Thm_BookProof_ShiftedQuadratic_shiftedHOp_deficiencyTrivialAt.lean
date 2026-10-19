-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_deficiencyTrivialAt
-- name    : BookProof.ShiftedQuadratic.shiftedHOp_deficiencyTrivialAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:26:36.35993+00:00
-- url     : https://prove2.me/theorems/71f6d81e-06ce-456c-a6a5-2c9533fa5a85
-- title:
--   `BookProof.ShiftedQuadratic.shiftedHOp_deficiencyTrivialAt` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (polyGaussCoreT (shiftVec c b) (b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.shiftedHOp_deficiencyTrivialAt` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) {z : ℂ} (hz : z.im ≠ 0) : DeficiencyTrivialAt (polyGaussCoreT (shiftVec c b) (boostVec c b')) (shiftedHOp (shiftVec c b) (boostVec c b') c b b') z
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.shiftedHOp_deficiencyTrivialAt`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.shiftedHOp_deficiencyTrivialAt
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

theorem BookProof.ShiftedQuadratic.shiftedHOp_deficiencyTrivialAt (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) {z : ℂ}
    (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCoreT (shiftVec c b) (boostVec c b'))
      (shiftedHOp (shiftVec c b) (boostVec c b') c b b') z := by sorry
