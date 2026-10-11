-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_coe_eq_pgLpT
-- name    : BookProof.ShiftedQuadratic.shiftedHOp_coe_eq_pgLpT
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:44:28.634604+00:00
-- url     : https://prove2.me/theorems/eacd8b74-30d0-4dce-b616-64cae6cec322
-- title:
--   `BookProof.ShiftedQuadratic.shiftedHOp_coe_eq_pgLpT` (a k : Vd d) (c b b' : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) : shiftedHOp a k c b b' (coreEquivT a k p) = pgLpT a k (shiftedH
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.shiftedHOp_coe_eq_pgLpT` (a k : Vd d) (c b b' : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) : shiftedHOp a k c b b' (coreEquivT a k p) = pgLpT a k (shiftedHPoly a k c b b' p)
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.shiftedHOp_coe_eq_pgLpT`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.shiftedHOp_coe_eq_pgLpT
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
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

theorem BookProof.ShiftedQuadratic.shiftedHOp_coe_eq_pgLpT (a k : Vd d) (c b b' : Fin d → ℝ)
    (p : MvPolynomial (Fin d) ℂ) :
    shiftedHOp a k c b b' (coreEquivT a k p) = pgLpT a k (shiftedHPoly a k c b b' p) := by sorry
