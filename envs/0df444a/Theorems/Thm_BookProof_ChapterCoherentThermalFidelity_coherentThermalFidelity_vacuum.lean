-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_coherentThermalFidelity_vacuum
-- name    : BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:15:36.943982+00:00
-- url     : https://prove2.me/theorems/66e5a0aa-20f3-4159-a3b4-e8e429542c24
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum` (lam : ℝ) : coherentThermalFidelity 0 lam = Real.exp (-lam)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum` (lam : ℝ) : coherentThermalFidelity 0 lam = Real.exp (-lam)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterCoherentTemperature
import Definitions.Def_ChapterCoherentFidelity
import Definitions.Def_ChapterDisplacedThermalOverlap
import Mathlib
import Definitions.Def_ChapterCoherentThermalFidelity
open BookProof.ChapterCoherentThermalFidelity


noncomputable section


open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum (lam : ℝ) :
    coherentThermalFidelity 0 lam = Real.exp (-lam) := by sorry
