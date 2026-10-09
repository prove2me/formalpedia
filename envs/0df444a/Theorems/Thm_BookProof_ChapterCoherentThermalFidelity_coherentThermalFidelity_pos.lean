-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_coherentThermalFidelity_pos
-- name    : BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:12:28.435294+00:00
-- url     : https://prove2.me/theorems/88982b71-3a84-455a-9250-365d38a0962d
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_pos` (h : 0 ≤ nbar) (lam : ℝ) : 0 < coherentThermalFidelity nbar lam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_pos` (h : 0 ≤ nbar) (lam : ℝ) : 0 < coherentThermalFidelity nbar lam
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_pos`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_pos
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

theorem BookProof.ChapterCoherentThermalFidelity.coherentThermalFidelity_pos (h : 0 ≤ nbar) (lam : ℝ) :
    0 < coherentThermalFidelity nbar lam := by sorry
