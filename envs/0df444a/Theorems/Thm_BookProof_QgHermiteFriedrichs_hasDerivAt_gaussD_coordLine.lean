-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_hasDerivAt_gaussD_coordLine
-- name    : BookProof.QgHermiteFriedrichs.hasDerivAt_gaussD_coordLine
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:53:36.726598+00:00
-- url     : https://prove2.me/theorems/30417889-a263-4bdb-afc5-834734e8ce1c
-- title:
--   The Lean 4 theorem `hasDerivAt_gaussD_coordLine` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_gaussD_coordLine` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.hasDerivAt_gaussD_coordLine
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

theorem BookProof.QgHermiteFriedrichs.hasDerivAt_gaussD_coordLine (x : Vd d) (j : Fin d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussD (coordLine x j s))
      (-(t / 2) * gaussD (coordLine x j t)) t := by sorry
