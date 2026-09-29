-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_inner_pgLp_pgLp
-- name    : BookProof.QgHermiteFriedrichs.inner_pgLp_pgLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:53:52.568976+00:00
-- url     : https://prove2.me/theorems/e0d16a73-8509-4251-82a2-91730938efbd
-- title:
--   The Lean 4 theorem `inner_pgLp_pgLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_pgLp_pgLp` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.inner_pgLp_pgLp
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

theorem BookProof.QgHermiteFriedrichs.inner_pgLp_pgLp (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (cpoly p * q) := by sorry
