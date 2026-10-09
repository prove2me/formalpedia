-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_dtOverlap_vacuum_width
-- name    : BookProof.ChapterCoherentThermalFidelity.dtOverlap_vacuum_width
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:16:17.362963+00:00
-- url     : https://prove2.me/theorems/a4ad61ab-594f-4585-b47c-1c1782a9ee1e
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.dtOverlap_vacuum_width` : ((0 : NNReal) : ℝ) + 1 / 2 + (((0 : NNReal) : ℝ) + 1 / 2) = coherentWidth + coherentWidth
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.dtOverlap_vacuum_width` : ((0 : NNReal) : ℝ) + 1 / 2 + (((0 : NNReal) : ℝ) + 1 / 2) = coherentWidth + coherentWidth
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.dtOverlap_vacuum_width`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.dtOverlap_vacuum_width
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

theorem BookProof.ChapterCoherentThermalFidelity.dtOverlap_vacuum_width :
    ((0 : NNReal) : ℝ) + 1 / 2 + (((0 : NNReal) : ℝ) + 1 / 2) = coherentWidth + coherentWidth := by sorry
