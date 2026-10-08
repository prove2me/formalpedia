-- Prove2me | Theorems.Thm_BookProof_FockInteractionStability_gap_persists_of_relative_form_bound
-- name    : BookProof.FockInteractionStability.gap_persists_of_relative_form_bound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T10:11:07.574652+00:00
-- url     : https://prove2.me/theorems/bf87902a-2c7c-40da-968e-79b0ef329e6e
-- title:
--   `BookProof.FockInteractionStability.gap_persists_of_relative_form_bound` {q v : E → ℝ} {S : Set E} {mu a b : ℝ} (ha : a ≤ 1) (hq : ∀ x ∈ S, mu * ‖x‖ ^ 2 ≤ q x) (hv : ∀ x, |v...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockInteractionStability`.
--
--   `BookProof.FockInteractionStability.gap_persists_of_relative_form_bound` {q v : E → ℝ} {S : Set E} {mu a b : ℝ} (ha : a ≤ 1) (hq : ∀ x ∈ S, mu * ‖x‖ ^ 2 ≤ q x) (hv : ∀ x, |v x| ≤ a * q x + b * ‖x‖ ^ 2) : ∀ x ∈ S, ((1 - a) * mu - b) * ‖x‖ ^ 2 ≤ q x + v x
--
--   Formalization note: Lean 4 identifier `BookProof.FockInteractionStability.gap_persists_of_relative_form_bound`.

-- Generated from ChapterFockInteractionStability.lean — theorem BookProof.FockInteractionStability.gap_persists_of_relative_form_bound
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

theorem BookProof.FockInteractionStability.gap_persists_of_relative_form_bound
    {q v : E → ℝ} {S : Set E} {mu a b : ℝ} (ha : a ≤ 1)
    (hq : ∀ x ∈ S, mu * ‖x‖ ^ 2 ≤ q x)
    (hv : ∀ x, |v x| ≤ a * q x + b * ‖x‖ ^ 2) :
    ∀ x ∈ S, ((1 - a) * mu - b) * ‖x‖ ^ 2 ≤ q x + v x := by sorry
