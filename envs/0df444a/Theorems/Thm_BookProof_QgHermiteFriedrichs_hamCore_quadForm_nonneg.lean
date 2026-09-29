-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_quadForm_nonneg
-- name    : BookProof.QgHermiteFriedrichs.hamCore_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:19:53.799862+00:00
-- url     : https://prove2.me/theorems/4dea66e3-0198-4afd-83d5-90eddf69f4bb
-- title:
--   The Lean 4 theorem `hamCore_quadForm_nonneg` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hamCore_quadForm_nonneg` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.hamCore_quadForm_nonneg
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

theorem BookProof.QgHermiteFriedrichs.hamCore_quadForm_nonneg (hWc : Continuous W) (hWb : ExpBounded W)
    (hW0 : ∀ x, 0 ≤ W x) (x : (polyGaussCore (d := d))) :
    0 ≤ quadForm (hamCore W hWc hWb) x := by sorry
