-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentFidelity_neg_log_fidelityC
-- name    : BookProof.ChapterCoherentFidelity.neg_log_fidelityC
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:51:49.190039+00:00
-- url     : https://prove2.me/theorems/792cbb9c-1dc1-4ba9-a342-34c5db42f9b7
-- title:
--   `BookProof.ChapterCoherentFidelity.neg_log_fidelityC` (q k : EuclideanSpace ℂ (Fin n)) : -Real.log (fidelityC q k) = ‖q - k‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentFidelity`.
--
--   `BookProof.ChapterCoherentFidelity.neg_log_fidelityC` (q k : EuclideanSpace ℂ (Fin n)) : -Real.log (fidelityC q k) = ‖q - k‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentFidelity.neg_log_fidelityC`.

-- Generated from ChapterCoherentFidelity.lean — theorem BookProof.ChapterCoherentFidelity.neg_log_fidelityC
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
open BookProof.ChapterCoherentFidelity


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

theorem BookProof.ChapterCoherentFidelity.neg_log_fidelityC (q k : EuclideanSpace ℂ (Fin n)) :
    -Real.log (fidelityC q k) = ‖q - k‖ ^ 2 := by sorry
