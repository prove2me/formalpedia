-- Prove2me | Theorems.Thm_BookProof_EnergyBandDecomposition_norm_mul_energy_sub_scalar_le
-- name    : BookProof.EnergyBandDecomposition.norm_mul_energy_sub_scalar_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:45:19.522159+00:00
-- url     : https://prove2.me/theorems/6594e882-40aa-48c6-aaeb-cb4e6dff0e05
-- title:
--   `BookProof.EnergyBandDecomposition.norm_mul_energy_sub_scalar_le` (hε : 0 < ε) (hx : x ∈ band E ε k) (z : ℂ) : ‖(E x : ℂ) * z - ((k : ℝ) * ε : ℝ) * z‖ ≤ ε * ‖z‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEnergyBandDecomposition`.
--
--   `BookProof.EnergyBandDecomposition.norm_mul_energy_sub_scalar_le` (hε : 0 < ε) (hx : x ∈ band E ε k) (z : ℂ) : ‖(E x : ℂ) * z - ((k : ℝ) * ε : ℝ) * z‖ ≤ ε * ‖z‖
--
--   Formalization note: Lean 4 identifier `BookProof.EnergyBandDecomposition.norm_mul_energy_sub_scalar_le`.

-- Generated from ChapterEnergyBandDecomposition.lean — theorem BookProof.EnergyBandDecomposition.norm_mul_energy_sub_scalar_le
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
open BookProof.EnergyBandDecomposition



open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

theorem BookProof.EnergyBandDecomposition.norm_mul_energy_sub_scalar_le (hε : 0 < ε) (hx : x ∈ band E ε k) (z : ℂ) :
    ‖(E x : ℂ) * z - ((k : ℝ) * ε : ℝ) * z‖ ≤ ε * ‖z‖ := by sorry
