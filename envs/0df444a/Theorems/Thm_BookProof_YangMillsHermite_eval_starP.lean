-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_eval_starP
-- name    : BookProof.YangMillsHermite.eval_starP
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:57:43.903416+00:00
-- url     : https://prove2.me/theorems/5c8988b3-9c30-4869-b05e-6e5bb44e26f7
-- title:
--   (p : MvPolynomial (Fin d) ℂ) (x : Vd d) : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p) = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.eval_starP` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.eval_starP
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.eval_starP (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p)
      = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by sorry
