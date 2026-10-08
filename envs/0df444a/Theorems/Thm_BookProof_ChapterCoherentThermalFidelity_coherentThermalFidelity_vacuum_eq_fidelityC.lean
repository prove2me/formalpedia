-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_coherentThermalFidelity_vacuum_eq_fidelityC
-- name    : BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum_eq_fidelityC
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:13:58.884437+00:00
-- url     : https://prove2.me/theorems/2afa6117-b253-4903-8dea-f577d5454cf8
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum_eq_fidelityC` {n : ℕ} (q k : EuclideanSpace ℂ (Fin n)) : coherentThermalFidelity 0 (‖q - k‖ ^ 2) = fidelity
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum_eq_fidelityC` {n : ℕ} (q k : EuclideanSpace ℂ (Fin n)) : coherentThermalFidelity 0 (‖q - k‖ ^ 2) = fidelityC q k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum_eq_fidelityC`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum_eq_fidelityC
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

theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_vacuum_eq_fidelityC {n : ℕ}
    (q k : EuclideanSpace ℂ (Fin n)) :
    coherentThermalFidelity 0 (‖q - k‖ ^ 2) = fidelityC q k := by sorry
