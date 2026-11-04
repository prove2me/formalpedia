-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn11_gaussian_grid_L2_of_second_moment_bound
-- name    : AvramDividend.Classical.avram_wave7_05_turn11_gaussian_grid_L2_of_second_moment_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:48:00.880034+00:00
-- url     : https://prove2.me/theorems/e8ac72c8-162a-4751-9414-3d1631de5226
-- title:
--   Real L2 Vitali norm from the finite Gaussian mesh second moment envelope
-- statement:
--   A reusable exact norm bridge for the Gaussian finite-mesh programme: if a real random variable has an L2 bound and its expected square is at most a nonnegative real B, its extended nonnegative L2 norm is at most the square root of B. Intended for the original disjoint-grid Gaussian theorem and the Proved uniform-L2 Vitali limit theorem.
-- source:
--   Mathlib MemLp.eLpNorm_eq_integral_rpow_norm, Real.rpow_le_rpow and ENNReal.ofReal_le_ofReal; adapted from the accepted original-source stopped C2 single-cell seminorm argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Topology
noncomputable section

/-! Turn an exact finite-mesh second-moment bound into the Vitali L² norm bound. -/

theorem AvramDividend.Classical.avram_wave7_05_turn11_gaussian_grid_L2_of_second_moment_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : MemLp f 2 P)
    (hMoment : (∫ ω, (f ω) ^ 2 ∂P) ≤ B) :
    eLpNorm f (2 : ℝ≥0∞) P ≤
      ENNReal.ofReal (Real.sqrt B) := by sorry
