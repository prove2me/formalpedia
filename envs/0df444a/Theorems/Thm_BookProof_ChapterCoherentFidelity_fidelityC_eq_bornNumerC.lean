-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_eq_bornNumerC
-- name    : BookProof.ChapterCoherentFidelity.fidelityC_eq_bornNumerC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:49:27.820218+00:00
-- url     : https://prove2.me/theorems/fc63a61e-da93-4fce-888f-969dba099162
-- title:
--   `BookProof.ChapterCoherentFidelity.fidelityC_eq_bornNumerC` (q k : EuclideanSpace ℂ (Fin n)) : fidelityC q k = bornNumerC q k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentFidelity`.
--
--   `BookProof.ChapterCoherentFidelity.fidelityC_eq_bornNumerC` (q k : EuclideanSpace ℂ (Fin n)) : fidelityC q k = bornNumerC q k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentFidelity.fidelityC_eq_bornNumerC`.

-- Generated from ChapterCoherentFidelity.lean — theorem BookProof.ChapterCoherentFidelity.fidelityC_eq_bornNumerC
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentFidelity


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

theorem BookProof.ChapterCoherentFidelity.fidelityC_eq_bornNumerC (q k : EuclideanSpace ℂ (Fin n)) :
    fidelityC q k = bornNumerC q k := by sorry
