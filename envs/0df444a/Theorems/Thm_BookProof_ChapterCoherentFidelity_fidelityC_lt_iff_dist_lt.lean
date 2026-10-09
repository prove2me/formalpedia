-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentFidelity_fidelityC_lt_iff_dist_lt
-- name    : BookProof.ChapterCoherentFidelity.fidelityC_lt_iff_dist_lt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:51:08.919007+00:00
-- url     : https://prove2.me/theorems/3eba70c5-9e93-4a77-bc8d-815d63c5d233
-- title:
--   `BookProof.ChapterCoherentFidelity.fidelityC_lt_iff_dist_lt` (q k k' : EuclideanSpace ℂ (Fin n)) : fidelityC q k < fidelityC q k' ↔ ‖q - k'‖ < ‖q - k‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentFidelity`.
--
--   `BookProof.ChapterCoherentFidelity.fidelityC_lt_iff_dist_lt` (q k k' : EuclideanSpace ℂ (Fin n)) : fidelityC q k < fidelityC q k' ↔ ‖q - k'‖ < ‖q - k‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentFidelity.fidelityC_lt_iff_dist_lt`.

-- Generated from ChapterCoherentFidelity.lean — theorem BookProof.ChapterCoherentFidelity.fidelityC_lt_iff_dist_lt
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterCoherentFidelity
open BookProof.ChapterCoherentFidelity


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterSoftmaxSharpness

variable {n m : ℕ}

theorem BookProof.ChapterCoherentFidelity.fidelityC_lt_iff_dist_lt (q k k' : EuclideanSpace ℂ (Fin n)) :
    fidelityC q k < fidelityC q k' ↔ ‖q - k'‖ < ‖q - k‖ := by sorry
