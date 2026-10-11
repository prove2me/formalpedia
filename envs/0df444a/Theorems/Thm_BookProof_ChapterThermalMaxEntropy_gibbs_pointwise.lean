-- Prove2me | Theorems.Thm_BookProof_ChapterThermalMaxEntropy_gibbs_pointwise
-- name    : BookProof.ChapterThermalMaxEntropy.gibbs_pointwise
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:06:07.919191+00:00
-- url     : https://prove2.me/theorems/5513aabb-c729-4df4-b18f-3895c3e94eb9
-- title:
--   `BookProof.ChapterThermalMaxEntropy.gibbs_pointwise` (h : 0 < nbar) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) : p * Real.log (thermalProb nbar n) - p * Real.log p ≤ thermalProb nbar n - p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalMaxEntropy`.
--
--   `BookProof.ChapterThermalMaxEntropy.gibbs_pointwise` (h : 0 < nbar) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) : p * Real.log (thermalProb nbar n) - p * Real.log p ≤ thermalProb nbar n - p
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalMaxEntropy.gibbs_pointwise`.

-- Generated from ChapterThermalMaxEntropy.lean — theorem BookProof.ChapterThermalMaxEntropy.gibbs_pointwise
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterBoseEinstein
import Mathlib
import Definitions.Def_ChapterThermalMaxEntropy
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterCoherentTemperature
open BookProof.ChapterThermalMaxEntropy


noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {nbar : ℝ}

theorem BookProof.ChapterThermalMaxEntropy.gibbs_pointwise (h : 0 < nbar) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    p * Real.log (thermalProb nbar n) - p * Real.log p ≤ thermalProb nbar n - p := by sorry
