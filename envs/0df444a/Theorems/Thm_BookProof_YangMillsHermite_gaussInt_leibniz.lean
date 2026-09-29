-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_gaussInt_leibniz
-- name    : BookProof.YangMillsHermite.gaussInt_leibniz
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:58:58.242065+00:00
-- url     : https://prove2.me/theorems/a9ed7beb-ad0f-4727-8517-2bdea5589094
-- title:
--   (j : Fin d) (P Q : MvPolynomial (Fin d) ℂ) : gaussInt (pderiv j P * Q) + gaussInt (P * pderiv j Q) = gaussInt (X j * (P * Q))
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.gaussInt_leibniz` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.gaussInt_leibniz
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.gaussInt_leibniz (j : Fin d) (P Q : MvPolynomial (Fin d) ℂ) :
    gaussInt (pderiv j P * Q) + gaussInt (P * pderiv j Q) = gaussInt (X j * (P * Q)) := by sorry
