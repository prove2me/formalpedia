-- Prove2me | Theorems.Thm_BookProof_EnergyBandDecomposition_mem_band_iff_floor
-- name    : BookProof.EnergyBandDecomposition.mem_band_iff_floor
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:44:17.558984+00:00
-- url     : https://prove2.me/theorems/37c83c80-bd8e-4a44-a73c-98ebe09c4af4
-- title:
--   `BookProof.EnergyBandDecomposition.mem_band_iff_floor` (hε : 0 < ε) (E : X → ℝ) (k : ℤ) (x : X) : x ∈ band E ε k ↔ k = ⌊E x / ε⌋
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEnergyBandDecomposition`.
--
--   `BookProof.EnergyBandDecomposition.mem_band_iff_floor` (hε : 0 < ε) (E : X → ℝ) (k : ℤ) (x : X) : x ∈ band E ε k ↔ k = ⌊E x / ε⌋
--
--   Formalization note: Lean 4 identifier `BookProof.EnergyBandDecomposition.mem_band_iff_floor`.

-- Generated from ChapterEnergyBandDecomposition.lean — theorem BookProof.EnergyBandDecomposition.mem_band_iff_floor
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
open BookProof.EnergyBandDecomposition



open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

theorem BookProof.EnergyBandDecomposition.mem_band_iff_floor (hε : 0 < ε) (E : X → ℝ) (k : ℤ) (x : X) :
    x ∈ band E ε k ↔ k = ⌊E x / ε⌋ := by sorry
