-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHPoly_eq_quadPoly
-- name    : BookProof.ShiftedQuadratic.shiftedHPoly_eq_quadPoly
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:26:12.476026+00:00
-- url     : https://prove2.me/theorems/2edac4cf-f1be-47c2-b860-1a54f1c03445
-- title:
--   `BookProof.ShiftedQuadratic.shiftedHPoly_eq_quadPoly` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) (p : MvPolynomial (Fin d) ℂ) : shiftedHPoly (shiftVec c b) (boostVec c b') c b b' p =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.shiftedHPoly_eq_quadPoly` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) (p : MvPolynomial (Fin d) ℂ) : shiftedHPoly (shiftVec c b) (boostVec c b') c b b' p = quadPoly c p + ((shiftConst c b b' : ℝ) : ℂ) • p
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.shiftedHPoly_eq_quadPoly`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.shiftedHPoly_eq_quadPoly
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
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

theorem BookProof.ShiftedQuadratic.shiftedHPoly_eq_quadPoly (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0)
    (p : MvPolynomial (Fin d) ℂ) :
    shiftedHPoly (shiftVec c b) (boostVec c b') c b b' p
      = quadPoly c p + ((shiftConst c b b' : ℝ) : ℂ) • p := by sorry
