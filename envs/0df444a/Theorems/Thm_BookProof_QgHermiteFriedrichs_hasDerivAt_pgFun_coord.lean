-- Prove2me | Theorems.Thm_BookProof_QgHermiteFriedrichs_hasDerivAt_pgFun_coord
-- name    : BookProof.QgHermiteFriedrichs.hasDerivAt_pgFun_coord
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:55:56.905863+00:00
-- url     : https://prove2.me/theorems/bf3a96a4-c6d9-413a-8c76-1c5924e6e7ba
-- title:
--   The Lean 4 theorem `hasDerivAt_pgFun_coord` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_pgFun_coord` in the `ChapterQgHermiteFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgHermiteFriedrichs.lean

-- Generated from ChapterQgHermiteFriedrichs.lean — theorem BookProof.QgHermiteFriedrichs.hasDerivAt_pgFun_coord
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

theorem BookProof.QgHermiteFriedrichs.hasDerivAt_pgFun_coord (p : MvPolynomial (Fin d) ℂ) (j : Fin d) (x : Vd d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => pgFun p (coordLine x j s))
      (pgFun (coreD j p) (coordLine x j t)) t := by sorry
