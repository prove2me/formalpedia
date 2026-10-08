-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentThermalFidelity_width_unique
-- name    : BookProof.ChapterCoherentThermalFidelity.width_unique
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:13:46.402984+00:00
-- url     : https://prove2.me/theorems/0b6d9cf1-f375-4b8e-8129-d97295c922f3
-- title:
--   `BookProof.ChapterCoherentThermalFidelity.width_unique` (h : 0 ≤ nbar) {w : ℝ} (hw : 0 < w) (hfid : ∀ lam : ℝ, coherentThermalFidelity nbar lam = Real.exp (-(lam / w)) / w) : w = n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentThermalFidelity`.
--
--   `BookProof.ChapterCoherentThermalFidelity.width_unique` (h : 0 ≤ nbar) {w : ℝ} (hw : 0 < w) (hfid : ∀ lam : ℝ, coherentThermalFidelity nbar lam = Real.exp (-(lam / w)) / w) : w = nbar + 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentThermalFidelity.width_unique`.

-- Generated from ChapterCoherentThermalFidelity.lean — theorem BookProof.ChapterCoherentThermalFidelity.width_unique
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

theorem BookProof.ChapterCoherentThermalFidelity.width_unique (h : 0 ≤ nbar) {w : ℝ} (hw : 0 < w)
    (hfid : ∀ lam : ℝ, coherentThermalFidelity nbar lam = Real.exp (-(lam / w)) / w) :
    w = nbar + 1 := by sorry
