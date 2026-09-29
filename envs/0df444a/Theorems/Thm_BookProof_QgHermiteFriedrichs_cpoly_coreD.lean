-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_cpoly_coreD
-- name    : BookProof.QgHermiteFriedrichs.cpoly_coreD
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:13:00.544901+00:00
-- url     : https://prove2.me/theorems/33b66ede-64be-4e76-b27d-3cdf1fab4ad2
-- title:
--   The Lean 4 theorem `cpoly_coreD` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `cpoly_coreD` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.cpoly_coreD
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterSirkBandLedger
open BookProof.QgHermiteFriedrichs







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

theorem BookProof.QgHermiteFriedrichs.cpoly_coreD (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    cpoly (coreD j p) = coreD j (cpoly p) := by sorry
