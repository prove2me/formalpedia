-- Prove2me | Theorems.Thm_BookProof_EnergyBandDecomposition_norm_evolution_sub_scalar_le
-- name    : BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T02:45:43.887984+00:00
-- url     : https://prove2.me/theorems/ffd27a2c-3082-4559-bb54-b1df063bd585
-- title:
--   `BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le` (hε : 0 < ε) (hx : x ∈ band E ε k) (t : ℝ) (z : ℂ) : ‖Complex.exp (-(Complex.I * (t * (E x : ℂ)))) * z - Complex.ex
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEnergyBandDecomposition`.
--
--   `BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le` (hε : 0 < ε) (hx : x ∈ band E ε k) (t : ℝ) (z : ℂ) : ‖Complex.exp (-(Complex.I * (t * (E x : ℂ)))) * z - Complex.exp (-(Complex.I * (t * ((((k : ℝ) * ε : ℝ)) : ℂ)))) * z‖ ≤ |t| * ε * ‖z‖
--
--   Formalization note: Lean 4 identifier `BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le`.

-- Generated from ChapterEnergyBandDecomposition.lean — theorem BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
open BookProof.EnergyBandDecomposition



open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

theorem BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le (hε : 0 < ε) (hx : x ∈ band E ε k) (t : ℝ) (z : ℂ) :
    ‖Complex.exp (-(Complex.I * (t * (E x : ℂ)))) * z
        - Complex.exp (-(Complex.I * (t * ((((k : ℝ) * ε : ℝ)) : ℂ)))) * z‖ ≤ |t| * ε * ‖z‖ := by sorry
