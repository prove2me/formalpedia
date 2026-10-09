-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_thermalOccupation_energy
-- name    : BookProof.ChapterCoherentOccupation.thermalOccupation_energy
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:55:27.095721+00:00
-- url     : https://prove2.me/theorems/4f2797bb-6cfb-4b66-a93a-e88afd260b96
-- title:
--   `BookProof.ChapterCoherentOccupation.thermalOccupation_energy` {nbar : ℝ} (h : 0 ≤ nbar) : ∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n = nbar + 1 / 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.thermalOccupation_energy` {nbar : ℝ} (h : 0 ≤ nbar) : ∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n = nbar + 1 / 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.thermalOccupation_energy`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.thermalOccupation_energy
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.thermalOccupation_energy {nbar : ℝ} (h : 0 ≤ nbar) :
    ∑' n : ℕ, ((n : ℝ) + 1 / 2) * thermalProb nbar n = nbar + 1 / 2 := by sorry
