-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_coherentBornC_cancel_q
-- name    : BookProof.ChapterCoherentOverlapComplex.coherentBornC_cancel_q
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:02:36.045724+00:00
-- url     : https://prove2.me/theorems/11b41131-cecd-479e-adb6-3ec897bf1edc
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.coherentBornC_cancel_q` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC q k j = Real.exp (-
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.coherentBornC_cancel_q` (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC q k j = Real.exp (-‖k j‖ ^ 2) * Real.exp (2 * (inner ℂ q (k j) : ℂ).re) / ∑ l, Real.exp (-‖k l‖ ^ 2) * Real.exp (2 * (inner ℂ q (k l) : ℂ).re)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.coherentBornC_cancel_q`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.coherentBornC_cancel_q
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.coherentBornC_cancel_q (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    bornWeightC q k j =
      Real.exp (-‖k j‖ ^ 2) * Real.exp (2 * (inner ℂ q (k j) : ℂ).re) /
        ∑ l, Real.exp (-‖k l‖ ^ 2) * Real.exp (2 * (inner ℂ q (k l) : ℂ).re) := by sorry
