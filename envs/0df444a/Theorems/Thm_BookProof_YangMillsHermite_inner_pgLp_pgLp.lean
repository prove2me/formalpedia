-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_inner_pgLp_pgLp
-- name    : BookProof.YangMillsHermite.inner_pgLp_pgLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:14:26.502209+00:00
-- url     : https://prove2.me/theorems/92da2f86-8da4-4ac2-bd08-dbda32ac7614
-- title:
--   (p q : MvPolynomial (Fin d) ℂ) : (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (starP p * q)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.inner_pgLp_pgLp` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.inner_pgLp_pgLp
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.inner_pgLp_pgLp (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (starP p * q) := by sorry
