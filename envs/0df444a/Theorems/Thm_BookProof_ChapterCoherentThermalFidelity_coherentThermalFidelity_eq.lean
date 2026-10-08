-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_coherentThermalFidelity_eq
-- name    : BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:12:15.285761+00:00
-- url     : https://prove2.me/theorems/1f8826b7-cfcb-4121-87fc-2cf0c8242f36
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq` (h : 0 ≤ nbar) (lam : ℝ) : coherentThermalFidelity nbar lam = Real.exp (-(lam / (nbar + 1))) / (nbar + 1)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq` (h : 0 ≤ nbar) (lam : ℝ) : coherentThermalFidelity nbar lam = Real.exp (-(lam / (nbar + 1))) / (nbar + 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq
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

theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq (h : 0 ≤ nbar) (lam : ℝ) :
    coherentThermalFidelity nbar lam = Real.exp (-(lam / (nbar + 1))) / (nbar + 1) := by sorry
