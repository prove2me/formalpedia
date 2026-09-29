-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_hasDerivAt_normSq_coordLine
-- name    : BookProof.QgHermiteFriedrichs.hasDerivAt_normSq_coordLine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:21:14.587899+00:00
-- url     : https://prove2.me/theorems/889db82d-ae59-4820-ad9e-4a128aedf2f7
-- title:
--   The Lean 4 theorem `hasDerivAt_normSq_coordLine` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_normSq_coordLine` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.hasDerivAt_normSq_coordLine
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

theorem BookProof.QgHermiteFriedrichs.hasDerivAt_normSq_coordLine (x : Vd d) (j : Fin d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖coordLine x j s‖ ^ 2) (2 * t) t := by sorry
