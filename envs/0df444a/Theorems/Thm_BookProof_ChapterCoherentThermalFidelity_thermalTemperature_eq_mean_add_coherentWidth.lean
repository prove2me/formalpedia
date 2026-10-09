-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_thermalTemperature_eq_mean_add_coherentWidth
-- name    : BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_mean_add_coherentWidth
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:16:07.161163+00:00
-- url     : https://prove2.me/theorems/b2390154-e3ee-4101-8ede-9eea6754ecc4
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_mean_add_coherentWidth` (nbar : ℝ) : thermalTemperature nbar = nbar + coherentWidth
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_mean_add_coherentWidth` (nbar : ℝ) : thermalTemperature nbar = nbar + coherentWidth
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_mean_add_coherentWidth`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_mean_add_coherentWidth
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterCoherentFidelity
import Definitions.Def_ChapterDisplacedThermalOverlap
import Mathlib
import Definitions.Def_ChapterCoherentThermalFidelity
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentThermalFidelity


noncomputable section


open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

theorem BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_mean_add_coherentWidth (nbar : ℝ) :
    thermalTemperature nbar = nbar + coherentWidth := by sorry
