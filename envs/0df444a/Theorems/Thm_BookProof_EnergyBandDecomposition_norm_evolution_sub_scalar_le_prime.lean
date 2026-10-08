-- Prove2me | Theorems.Thm_BookProof_EnergyBandDecomposition_norm_evolution_sub_scalar_le_prime
-- name    : BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le_prime
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T02:45:39.810089+00:00
-- url     : https://prove2.me/theorems/a7f35df8-7fb8-4695-af3c-ff8e081f0189
-- title:
--   BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le'
-- statement:
--   BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le'

-- Generated from ChapterEnergyBandDecomposition.lean — theorem BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le'
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
open BookProof.EnergyBandDecomposition



open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

theorem BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le_prime {a : ℝ} (t c : ℝ) (z : ℂ) (h : |a - c| ≤ ε) :
    ‖Complex.exp (-(Complex.I * (t * a))) * z
        - Complex.exp (-(Complex.I * (t * c))) * z‖ ≤ |t| * ε * ‖z‖ := by sorry
