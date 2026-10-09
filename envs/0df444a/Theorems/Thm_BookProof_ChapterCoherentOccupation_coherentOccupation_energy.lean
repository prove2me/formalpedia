-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_energy
-- name    : BookProof.ChapterCoherentOccupation.coherentOccupation_energy
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:55:01.314906+00:00
-- url     : https://prove2.me/theorems/936dde02-4e95-45a5-a987-a3e9e9ab3dd8
-- title:
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_energy` (lam : ℝ) : ∑' n : ℕ, ((n : ℝ) + 1 / 2) * coherentOccupation lam n = lam + 1 / 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOccupation`.
--
--   `BookProof.ChapterCoherentOccupation.coherentOccupation_energy` (lam : ℝ) : ∑' n : ℕ, ((n : ℝ) + 1 / 2) * coherentOccupation lam n = lam + 1 / 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOccupation.coherentOccupation_energy`.

-- Generated from ChapterCoherentOccupation.lean — theorem BookProof.ChapterCoherentOccupation.coherentOccupation_energy
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation


noncomputable section


open Real Nat ProbabilityTheory

theorem BookProof.ChapterCoherentOccupation.coherentOccupation_energy (lam : ℝ) :
    ∑' n : ℕ, ((n : ℝ) + 1 / 2) * coherentOccupation lam n = lam + 1 / 2 := by sorry
