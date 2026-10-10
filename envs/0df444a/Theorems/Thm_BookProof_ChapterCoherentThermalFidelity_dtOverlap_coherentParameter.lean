-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_dtOverlap_coherentParameter
-- name    : BookProof.ChapterCoherentThermalFidelity.dtOverlap_coherentParameter
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:14:21.987999+00:00
-- url     : https://prove2.me/theorems/012c2f98-e7c8-471f-94b4-62c23361db0b
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.dtOverlap_coherentParameter` (nb : NNReal) (a b : ℝ) : dtOverlap nb (Real.sqrt 2 * a) (Real.sqrt 2 * b) = Real.exp (-((a - b) ^ 2 / (((nb
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.dtOverlap_coherentParameter` (nb : NNReal) (a b : ℝ) : dtOverlap nb (Real.sqrt 2 * a) (Real.sqrt 2 * b) = Real.exp (-((a - b) ^ 2 / (((nb : ℝ) + 1 / 2) + ((nb : ℝ) + 1 / 2)))) / Real.sqrt (4 * π * ((nb : ℝ) + 1 / 2))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.dtOverlap_coherentParameter`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.dtOverlap_coherentParameter
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterCoherentTemperature
import Definitions.Def_ChapterCoherentFidelity
import Mathlib
import Definitions.Def_ChapterCoherentThermalFidelity
import Definitions.Def_ChapterDisplacedThermalOverlap
open BookProof.ChapterDisplacedThermalOverlap
open BookProof.ChapterCoherentThermalFidelity


noncomputable section


open BookProof.ChapterCoherentOccupation BookProof.ChapterCoherentTemperature
open BookProof.ChapterCoherentFidelity BookProof.ChapterDisplacedThermalOverlap
open Real

variable {nbar lam : ℝ}

theorem BookProof.ChapterCoherentThermalFidelity.dtOverlap_coherentParameter (nb : NNReal) (a b : ℝ) :
    dtOverlap nb (Real.sqrt 2 * a) (Real.sqrt 2 * b)
      = Real.exp (-((a - b) ^ 2 / (((nb : ℝ) + 1 / 2) + ((nb : ℝ) + 1 / 2))))
        / Real.sqrt (4 * π * ((nb : ℝ) + 1 / 2)) := by sorry
