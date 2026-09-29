-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_starP_momOp
-- name    : BookProof.YangMillsHermite.starP_momOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:24:56.007467+00:00
-- url     : https://prove2.me/theorems/18d29afe-6027-4480-971e-6889093147d2
-- title:
--   (j : Fin d) (p : MvPolynomial (Fin d) ℂ) : starP (momOp j p) = Complex.I • (pderiv j (starP p) - ((1 / 2 : ℝ) : ℂ) • (X j * starP p))
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.starP_momOp` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.starP_momOp
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.starP_momOp (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (momOp j p)
      = Complex.I • (pderiv j (starP p) - ((1 / 2 : ℝ) : ℂ) • (X j * starP p)) := by sorry
