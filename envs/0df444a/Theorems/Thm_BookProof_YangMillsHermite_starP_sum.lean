-- Prove2me | Theorems.Thm_BookProof_YangMillsHermite_starP_sum
-- name    : BookProof.YangMillsHermite.starP_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T01:07:58.679928+00:00
-- url     : https://prove2.me/theorems/36d9edc3-54fb-4b19-ab27-4372e0461fb3
-- title:
--   {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) : starP (∑ i ∈ s, f i) = ∑ i ∈ s, starP (f i)
-- statement:
--   Lean 4 theorem `BookProof.YangMillsHermite.starP_sum` (module `BookProof.YangMillsHermite`), source chapter `BookProof/ChapterYangMillsHermite.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsHermite.lean

-- Generated from ChapterYangMillsHermite.lean — theorem BookProof.YangMillsHermite.starP_sum
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite







open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

theorem BookProof.YangMillsHermite.starP_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    starP (∑ i ∈ s, f i) = ∑ i ∈ s, starP (f i) := by sorry
