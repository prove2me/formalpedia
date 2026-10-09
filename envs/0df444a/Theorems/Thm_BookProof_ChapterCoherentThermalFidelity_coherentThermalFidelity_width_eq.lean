-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_coherentThermalFidelity_width_eq
-- name    : BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_width_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:13:18.639986+00:00
-- url     : https://prove2.me/theorems/9f8708f7-c480-401b-a05d-ed22c3b09241
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_width_eq` (nbar : ℝ) : nbar + 1 = thermalTemperature nbar + coherentWidth
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_width_eq` (nbar : ℝ) : nbar + 1 = thermalTemperature nbar + coherentWidth
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_width_eq`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_width_eq
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

theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_width_eq (nbar : ℝ) :
    nbar + 1 = thermalTemperature nbar + coherentWidth := by sorry
