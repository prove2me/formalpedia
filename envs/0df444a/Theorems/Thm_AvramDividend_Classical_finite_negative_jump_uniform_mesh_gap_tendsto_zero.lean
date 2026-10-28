-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_negative_jump_uniform_mesh_gap_tendsto_zero
-- name    : AvramDividend.Classical.finite_negative_jump_uniform_mesh_gap_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:37:29.599491+00:00
-- url     : https://prove2.me/theorems/aed9aac7-d7d8-4f0a-b868-7d6aa023d160
-- title:
--   The finite-activity Lévy uniform-mesh exponential deficit vanishes as the mesh refines
-- statement:
--   For finite negative-jump intensity, N times the exponential-survival gap between the actual Lévy Laplace deficit at N and its finite limiting intensity, calculated on a time interval of length T/N, tends to zero. This is the analytic limiting step needed to rule out survival with a positive drift deficit.
-- source:
--   Proved finite-negative-jump exponential-deficit convergence and bounds, and the exponential-gap mesh inequality. Avram, Palmowski and Pistorius (2007) Section 3.3.

import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exponential_deficit_bounds_nat
import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exponential_deficit_limit_nat
import Theorems.Thm_AvramDividend_Classical_finite_activity_uniform_mesh_exp_gap_le_intensity_gap
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
open AvramDividend.Classical MeasureTheory Filter Set Topology

theorem AvramDividend.Classical.finite_negative_jump_uniform_mesh_gap_tendsto_zero
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 ≤ T) :
    Tendsto
      (fun N : ℕ =>
        (N : ℝ) *
          (Real.exp (-(T / (N : ℝ) *
            ∫ y in Iio (0 : ℝ), (1 - Real.exp ((N : ℝ) * y)) ∂ν)) -
            Real.exp (-(T / (N : ℝ) *
              (ν (Iio (0 : ℝ))).toReal))))
      atTop (𝓝 0) := by sorry
