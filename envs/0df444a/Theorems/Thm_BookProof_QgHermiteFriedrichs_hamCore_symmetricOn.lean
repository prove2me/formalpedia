-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_hamCore_symmetricOn
-- name    : BookProof.QgHermiteFriedrichs.hamCore_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:55:52.029858+00:00
-- url     : https://prove2.me/theorems/bc063b31-21ca-41eb-bf18-c9530bc3cad4
-- title:
--   The Lean 4 theorem `hamCore_symmetricOn` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hamCore_symmetricOn` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.hamCore_symmetricOn
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

theorem BookProof.QgHermiteFriedrichs.hamCore_symmetricOn (hWc : Continuous W) (hWb : ExpBounded W) :
    SymmetricOn (polyGaussCore (d := d)) (hamCore W hWc hWb) := by sorry
