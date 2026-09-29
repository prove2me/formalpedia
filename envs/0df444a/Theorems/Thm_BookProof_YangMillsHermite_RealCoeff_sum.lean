-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_sum
-- name    : BookProof.YangMillsHermite.RealCoeff.sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T03:45:58.134792+00:00
-- url     : https://prove2.me/theorems/1a9f7222-aaeb-4e9b-a837-212cbf5a4e7d
-- title:
--   {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Fin d) ℂ} (h : ∀ i ∈ s, RealCoeff (f i)) : RealCoeff (∑ i ∈ s, f i)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.RealCoeff.sum` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.RealCoeff.sum
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.RealCoeff.sum {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Fin d) ℂ}
    (h : ∀ i ∈ s, RealCoeff (f i)) : RealCoeff (∑ i ∈ s, f i) := by sorry
