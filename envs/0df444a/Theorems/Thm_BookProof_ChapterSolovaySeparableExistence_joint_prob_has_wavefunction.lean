-- Prove2me | Theorems.Thm_BookProof_ChapterSolovaySeparableExistence_joint_prob_has_wavefunction
-- name    : BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:45:45.658846+00:00
-- url     : https://prove2.me/theorems/ef9c48a6-1893-4b98-b5a3-8d935f175320
-- title:
--   `BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction` {Z : Type*} [Fintype Z] (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) : ∃ Ψ : Z → ℂ, (∀ z,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovaySeparableExistence`.
--
--   `BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction` {Z : Type*} [Fintype Z] (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) : ∃ Ψ : Z → ℂ, (∀ z, ‖Ψ z‖ ^ 2 = p z) ∧ ∑ z, ‖Ψ z‖ ^ 2 = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction`.

-- Generated from ChapterSolovaySeparableExistence.lean — theorem BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction
import Definitions.Def_ChapterSolovayCoordinates
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence


noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

theorem BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction {Z : Type*} [Fintype Z] (p : Z → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    ∃ Ψ : Z → ℂ, (∀ z, ‖Ψ z‖ ^ 2 = p z) ∧ ∑ z, ‖Ψ z‖ ^ 2 = 1 := by sorry
