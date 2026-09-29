-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_quadForm_ge
-- name    : BookProof.QgHermiteFriedrichs.hamCore_quadForm_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:56:58.822445+00:00
-- url     : https://prove2.me/theorems/5fc27226-2d04-4727-909b-3c69f55cb5c5
-- title:
--   The Lean 4 theorem `hamCore_quadForm_ge` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hamCore_quadForm_ge` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.hamCore_quadForm_ge
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterRitzCertificate
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

theorem BookProof.QgHermiteFriedrichs.hamCore_quadForm_ge (hWc : Continuous W) (hWb : ExpBounded W) (c : ℝ)
    (hlb : ∀ x, -c ≤ W x) (x : (polyGaussCore (d := d))) :
    -c * ‖(x : L2d d)‖ ^ 2 ≤ quadForm (hamCore W hWc hWb) x := by sorry
