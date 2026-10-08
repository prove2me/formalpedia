-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_eq_one_iff
-- name    : BookProof.ChapterCoherentFidelity.fidelityC_eq_one_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:51:20.163248+00:00
-- url     : https://prove2.me/theorems/d36a8e73-f5dd-42a9-af23-312db6868916
-- title:
--   `BookProof.ChapterCoherentFidelity.fidelityC_eq_one_iff` (q k : EuclideanSpace ℂ (Fin n)) : fidelityC q k = 1 ↔ q = k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentFidelity`.
--
--   `BookProof.ChapterCoherentFidelity.fidelityC_eq_one_iff` (q k : EuclideanSpace ℂ (Fin n)) : fidelityC q k = 1 ↔ q = k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentFidelity.fidelityC_eq_one_iff`.

-- Generated from ChapterCoherentFidelity.lean — theorem BookProof.ChapterCoherentFidelity.fidelityC_eq_one_iff
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
open BookProof.ChapterCoherentFidelity


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

theorem BookProof.ChapterCoherentFidelity.fidelityC_eq_one_iff (q k : EuclideanSpace ℂ (Fin n)) :
    fidelityC q k = 1 ↔ q = k := by sorry
