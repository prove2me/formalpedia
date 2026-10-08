-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_thermalTemperature_eq_energy_expectation
-- name    : BookProof.ChapterCoherentOccupation.thermalTemperature_eq_energy_expectation
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:55:42.544044+00:00
-- url     : https://prove2.me/theorems/1c7a1a17-a186-4a14-bcd3-dbfe8d9bd006
-- title:
--   `BookProof.ChapterCoherentOccupation.thermalTemperature_eq_energy_expectation` {nbar : ℝ} (h : 0 ≤ nbar) : thermalTemperature nbar = ∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.thermalTemperature_eq_energy_expectation` {nbar : ℝ} (h : 0 ≤ nbar) : thermalTemperature nbar = ∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.thermalTemperature_eq_energy_expectation`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.thermalTemperature_eq_energy_expectation
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.thermalTemperature_eq_energy_expectation {nbar : ℝ} (h : 0 ≤ nbar) :
    thermalTemperature nbar = ∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n := by sorry
