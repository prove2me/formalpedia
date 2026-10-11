-- Prove2me | Theorems.Thm_BookProof_ChapterThermalMaxEntropy_shannonEntropy_le_thermalEntropy
-- name    : BookProof.ChapterThermalMaxEntropy.shannonEntropy_le_thermalEntropy
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:06:13.375893+00:00
-- url     : https://prove2.me/theorems/020abbb2-d302-4b81-b903-afa0905c1b7c
-- title:
--   `BookProof.ChapterThermalMaxEntropy.shannonEntropy_le_thermalEntropy` (h : 0 < nbar) (s : Finset ℕ) (p : ℕ → ℝ) (hp : ∀ n ∈ s, 0 ≤ p n) (hsum : ∑ n ∈ s, p n = 1) (hmean : ∑...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterThermalMaxEntropy`.
--
--   `BookProof.ChapterThermalMaxEntropy.shannonEntropy_le_thermalEntropy` (h : 0 < nbar) (s : Finset ℕ) (p : ℕ → ℝ) (hp : ∀ n ∈ s, 0 ≤ p n) (hsum : ∑ n ∈ s, p n = 1) (hmean : ∑ n ∈ s, (n : ℝ) * p n = nbar) : -∑ n ∈ s, p n * Real.log (p n) ≤ thermalEntropy nbar
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterThermalMaxEntropy.shannonEntropy_le_thermalEntropy`.

-- Generated from ChapterThermalMaxEntropy.lean — theorem BookProof.ChapterThermalMaxEntropy.shannonEntropy_le_thermalEntropy
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

theorem BookProof.ChapterThermalMaxEntropy.shannonEntropy_le_thermalEntropy (h : 0 < nbar) (s : Finset ℕ) (p : ℕ → ℝ)
    (hp : ∀ n ∈ s, 0 ≤ p n) (hsum : ∑ n ∈ s, p n = 1)
    (hmean : ∑ n ∈ s, (n : ℝ) * p n = nbar) :
    -∑ n ∈ s, p n * Real.log (p n) ≤ thermalEntropy nbar := by sorry
