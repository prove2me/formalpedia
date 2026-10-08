-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_fidelityC_width
-- name    : BookProof.ChapterCoherentThermalFidelity.fidelityC_width
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:12:59.58124+00:00
-- url     : https://prove2.me/theorems/b36cce68-fdad-4381-8e10-e41bb41ba87a
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.fidelityC_width` {n : ℕ} (q k : EuclideanSpace ℂ (Fin n)) : fidelityC q k = Real.exp (-(‖q - k‖ ^ 2 / (coherentWidth + coherentWidth)))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.fidelityC_width` {n : ℕ} (q k : EuclideanSpace ℂ (Fin n)) : fidelityC q k = Real.exp (-(‖q - k‖ ^ 2 / (coherentWidth + coherentWidth)))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.fidelityC_width`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.fidelityC_width
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

theorem BookProof.ChapterCoherentThermalFidelity.fidelityC_width {n : ℕ} (q k : EuclideanSpace ℂ (Fin n)) :
    fidelityC q k = Real.exp (-(‖q - k‖ ^ 2 / (coherentWidth + coherentWidth))) := by sorry
