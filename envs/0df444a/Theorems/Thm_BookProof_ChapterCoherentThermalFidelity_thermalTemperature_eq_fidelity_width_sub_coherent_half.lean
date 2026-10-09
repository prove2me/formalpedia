-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_thermalTemperature_eq_fidelity_width_sub_coherent_half
-- name    : BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_fidelity_width_sub_coherent_half
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:13:48.073985+00:00
-- url     : https://prove2.me/theorems/aefa0bfb-959b-4c01-901f-f47b818a618f
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_fidelity_width_sub_coherent_half` (h : 0 ≤ nbar) {w : ℝ} (hw : 0 < w) (hfid : ∀ lam : ℝ, coherentThermalFidelity nba
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_fidelity_width_sub_coherent_half` (h : 0 ≤ nbar) {w : ℝ} (hw : 0 < w) (hfid : ∀ lam : ℝ, coherentThermalFidelity nbar lam = Real.exp (-(lam / w)) / w) : thermalTemperature nbar = w - coherentWidth
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_fidelity_width_sub_coherent_half`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_fidelity_width_sub_coherent_half
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

theorem BookProof.ChapterCoherentThermalFidelity.thermalTemperature_eq_fidelity_width_sub_coherent_half (h : 0 ≤ nbar)
    {w : ℝ} (hw : 0 < w)
    (hfid : ∀ lam : ℝ, coherentThermalFidelity nbar lam = Real.exp (-(lam / w)) / w) :
    thermalTemperature nbar = w - coherentWidth := by sorry
