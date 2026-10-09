-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_coherentThermalFidelity_eq_temperature_form
-- name    : BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq_temperature_form
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:13:23.045097+00:00
-- url     : https://prove2.me/theorems/a222d5f4-323d-43ff-a082-e64ebb1ddf02
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq_temperature_form` (h : 0 ≤ nbar) (lam : ℝ) : coherentThermalFidelity nbar lam = Real.exp (-(lam / (thermalTempe
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq_temperature_form` (h : 0 ≤ nbar) (lam : ℝ) : coherentThermalFidelity nbar lam = Real.exp (-(lam / (thermalTemperature nbar + coherentWidth))) / (thermalTemperature nbar + coherentWidth)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq_temperature_form`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq_temperature_form
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

theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_eq_temperature_form (h : 0 ≤ nbar) (lam : ℝ) :
    coherentThermalFidelity nbar lam
      = Real.exp (-(lam / (thermalTemperature nbar + coherentWidth)))
        / (thermalTemperature nbar + coherentWidth) := by sorry
