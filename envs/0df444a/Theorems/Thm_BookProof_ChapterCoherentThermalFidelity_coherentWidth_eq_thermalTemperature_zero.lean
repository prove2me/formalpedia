-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_coherentWidth_eq_thermalTemperature_zero
-- name    : BookProof.ChapterCoherentThermalFidelity.coherentWidth_eq_thermalTemperature_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:12:40.701975+00:00
-- url     : https://prove2.me/theorems/581e2fec-bc7f-4efb-8184-f01effee4ec7
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.coherentWidth_eq_thermalTemperature_zero` : coherentWidth = thermalTemperature 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.coherentWidth_eq_thermalTemperature_zero` : coherentWidth = thermalTemperature 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.coherentWidth_eq_thermalTemperature_zero`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.coherentWidth_eq_thermalTemperature_zero
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

theorem BookProof.ChapterCoherentThermalFidelity.coherentWidth_eq_thermalTemperature_zero :
    coherentWidth = thermalTemperature 0 := by sorry
