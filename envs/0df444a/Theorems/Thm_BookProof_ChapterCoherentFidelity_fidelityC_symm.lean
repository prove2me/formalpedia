-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_symm
-- name    : BookProof.ChapterCoherentFidelity.fidelityC_symm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:50:02.638352+00:00
-- url     : https://prove2.me/theorems/a7eea122-d30b-40c2-8d24-072378f4e88c
-- title:
--   `BookProof.ChapterCoherentFidelity.fidelityC_symm` (q k : EuclideanSpace ℂ (Fin n)) : fidelityC q k = fidelityC k q
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentFidelity`.
--
--   `BookProof.ChapterCoherentFidelity.fidelityC_symm` (q k : EuclideanSpace ℂ (Fin n)) : fidelityC q k = fidelityC k q
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentFidelity.fidelityC_symm`.

-- Generated from ChapterCoherentFidelity.lean — theorem BookProof.ChapterCoherentFidelity.fidelityC_symm
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
open BookProof.ChapterCoherentFidelity


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

theorem BookProof.ChapterCoherentFidelity.fidelityC_symm (q k : EuclideanSpace ℂ (Fin n)) : fidelityC q k = fidelityC k q := by sorry
