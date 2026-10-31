-- Prove2me | Theorems.Thm_BookProof_ChapterSolovaySeparableExistence_joint_prob_has_wavefunction_prod
-- name    : BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction_prod
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T22:45:48.247729+00:00
-- url     : https://prove2.me/theorems/917ec832-3a0b-491e-b2df-1abd2da0f736
-- title:
--   `BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction_prod` {X Y : Type*} [Fintype X] [Fintype Y] (p : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) : ∃ Ψ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSolovaySeparableExistence`.
--
--   `BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction_prod` {X Y : Type*} [Fintype X] [Fintype Y] (p : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) : ∃ Ψ : X × Y → ℂ, (∀ z, ‖Ψ z‖ ^ 2 = p z) ∧ ∑ z, ‖Ψ z‖ ^ 2 = 1 ∧ ∀ x : X, (∑ y : Y, ‖Ψ (x, y)‖ ^ 2) = ∑ y : Y, p (x, y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction_prod`.

-- Generated from ChapterSolovaySeparableExistence.lean — theorem BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction_prod
import Definitions.Def_ChapterSolovayCoordinates
import Mathlib
import Definitions.Def_ChapterSolovaySeparableExistence


noncomputable section

open MeasureTheory ProbabilityTheory


open BookProof.ChapterSolovayCoordinates

theorem BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction_prod {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X × Y → ℝ) (hp : ∀ z, 0 ≤ p z) (hsum : ∑ z, p z = 1) :
    ∃ Ψ : X × Y → ℂ, (∀ z, ‖Ψ z‖ ^ 2 = p z) ∧ ∑ z, ‖Ψ z‖ ^ 2 = 1 ∧
      ∀ x : X, (∑ y : Y, ‖Ψ (x, y)‖ ^ 2) = ∑ y : Y, p (x, y) := by sorry
