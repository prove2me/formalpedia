-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_dtOverlap_width_eq_two_tau
-- name    : BookProof.ChapterCoherentThermalFidelity.dtOverlap_width_eq_two_tau
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:14:13.63291+00:00
-- url     : https://prove2.me/theorems/c079c44c-19ea-4752-b404-27cf729926fb
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.dtOverlap_width_eq_two_tau` (nb : NNReal) : ((nb : ℝ) + 1 / 2) + ((nb : ℝ) + 1 / 2) = thermalTemperature (nb : ℝ) + thermalTemperature (nb
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.dtOverlap_width_eq_two_tau` (nb : NNReal) : ((nb : ℝ) + 1 / 2) + ((nb : ℝ) + 1 / 2) = thermalTemperature (nb : ℝ) + thermalTemperature (nb : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.dtOverlap_width_eq_two_tau`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.dtOverlap_width_eq_two_tau
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

theorem BookProof.ChapterCoherentThermalFidelity.dtOverlap_width_eq_two_tau (nb : NNReal) :
    ((nb : ℝ) + 1 / 2) + ((nb : ℝ) + 1 / 2)
      = thermalTemperature (nb : ℝ) + thermalTemperature (nb : ℝ) := by sorry
