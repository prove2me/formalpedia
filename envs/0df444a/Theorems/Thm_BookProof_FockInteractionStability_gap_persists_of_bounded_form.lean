-- Prove2me | Theorems.Thm_BookProof_FockInteractionStability_gap_persists_of_bounded_form
-- name    : BookProof.FockInteractionStability.gap_persists_of_bounded_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T10:11:08.032642+00:00
-- url     : https://prove2.me/theorems/ca457b6c-d44d-46b5-8334-9cd7bc20f80b
-- title:
--   `BookProof.FockInteractionStability.gap_persists_of_bounded_form` {q v : E → ℝ} {S : Set E} {mu b : ℝ} (hq : ∀ x ∈ S, mu * ‖x‖ ^ 2 ≤ q x) (hv : ∀ x, |v x| ≤ b * ‖x‖ ^ 2)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockInteractionStability`.
--
--   `BookProof.FockInteractionStability.gap_persists_of_bounded_form` {q v : E → ℝ} {S : Set E} {mu b : ℝ} (hq : ∀ x ∈ S, mu * ‖x‖ ^ 2 ≤ q x) (hv : ∀ x, |v x| ≤ b * ‖x‖ ^ 2) : ∀ x ∈ S, (mu - b) * ‖x‖ ^ 2 ≤ q x + v x
--
--   Formalization note: Lean 4 identifier `BookProof.FockInteractionStability.gap_persists_of_bounded_form`.

-- Generated from ChapterFockInteractionStability.lean — theorem BookProof.FockInteractionStability.gap_persists_of_bounded_form
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockInteractionStability
open BookProof.FockInteractionStability

variable {E : Type*} [NormedAddCommGroup E]


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockInteractionStability.gap_persists_of_bounded_form
    {q v : E → ℝ} {S : Set E} {mu b : ℝ}
    (hq : ∀ x ∈ S, mu * ‖x‖ ^ 2 ≤ q x)
    (hv : ∀ x, |v x| ≤ b * ‖x‖ ^ 2) :
    ∀ x ∈ S, (mu - b) * ‖x‖ ^ 2 ≤ q x + v x := by sorry
