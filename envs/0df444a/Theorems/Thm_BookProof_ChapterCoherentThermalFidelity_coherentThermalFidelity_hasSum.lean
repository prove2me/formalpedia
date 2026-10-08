-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_coherentThermalFidelity_hasSum
-- name    : BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_hasSum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:11:51.120059+00:00
-- url     : https://prove2.me/theorems/c8cf6274-bde7-4595-9ed0-f9e081923bfa
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_hasSum` (h : 0 ≤ nbar) (lam : ℝ) : HasSum (fun n : ℕ => coherentOccupation lam n * thermalProb nbar n) (Real.exp (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_hasSum` (h : 0 ≤ nbar) (lam : ℝ) : HasSum (fun n : ℕ => coherentOccupation lam n * thermalProb nbar n) (Real.exp (-(lam / (nbar + 1))) / (nbar + 1))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_hasSum`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_hasSum
import Definitions.Def_ChapterCoherentFidelity
import Definitions.Def_ChapterDisplacedThermalOverlap
import Mathlib
import Definitions.Def_ChapterCoherentThermalFidelity
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentOccupation
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentThermalFidelity


noncomputable section


open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_hasSum (h : 0 ≤ nbar) (lam : ℝ) :
    HasSum (fun n : ℕ => coherentOccupation lam n * thermalProb nbar n)
      (Real.exp (-(lam / (nbar + 1))) / (nbar + 1)) := by sorry
