-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_le_iff_dist_le
-- name    : BookProof.ChapterCoherentFidelity.fidelityC_le_iff_dist_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:50:54.076765+00:00
-- url     : https://prove2.me/theorems/0dbe011a-8ae4-41bb-95f7-def902475937
-- title:
--   `BookProof.ChapterCoherentFidelity.fidelityC_le_iff_dist_le` (q k k' : EuclideanSpace ℂ (Fin n)) : fidelityC q k ≤ fidelityC q k' ↔ ‖q - k'‖ ≤ ‖q - k‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentFidelity`.
--
--   `BookProof.ChapterCoherentFidelity.fidelityC_le_iff_dist_le` (q k k' : EuclideanSpace ℂ (Fin n)) : fidelityC q k ≤ fidelityC q k' ↔ ‖q - k'‖ ≤ ‖q - k‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentFidelity.fidelityC_le_iff_dist_le`.

-- Generated from ChapterCoherentFidelity.lean — theorem BookProof.ChapterCoherentFidelity.fidelityC_le_iff_dist_le
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
open BookProof.ChapterCoherentFidelity


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

theorem BookProof.ChapterCoherentFidelity.fidelityC_le_iff_dist_le (q k k' : EuclideanSpace ℂ (Fin n)) :
    fidelityC q k ≤ fidelityC q k' ↔ ‖q - k'‖ ≤ ‖q - k‖ := by sorry
