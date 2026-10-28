-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_activity_mesh_probability_bound_forces_zero
-- name    : AvramDividend.Classical.finite_activity_mesh_probability_bound_forces_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:57:34.889771+00:00
-- url     : https://prove2.me/theorems/9a94a3d5-e193-4f56-9143-3e167a6df487
-- title:
--   Finite-activity uniform-mesh probability domination forces the exceptional event to vanish
-- statement:
--   Under finite negative Lévy jump intensity, if a nonnegative real event probability is eventually dominated by exp(a) times N times the exact small-time Laplace-minus-zero-atom gap, then that probability is zero. This transfers the accepted analytic mesh convergence into the stochastic zero-barrier survivor-deficit argument.
-- source:
--   Previously Proved finite_negative_jump_uniform_mesh_gap_tendsto_zero; Avram, Palmowski and Pistorius (2007) §3.3.

import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_uniform_mesh_gap_tendsto_zero
import Mathlib.Topology.Order.Basic
open AvramDividend.Classical Filter MeasureTheory Set Topology

theorem AvramDividend.Classical.finite_activity_mesh_probability_bound_forces_zero
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (T a c : ℝ) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hBound : ∀ᶠ N : ℕ in atTop,
      c ≤ Real.exp a *
        ((N : ℝ) *
          (Real.exp (-(T / (N : ℝ) *
            ∫ y in Iio (0 : ℝ), (1 - Real.exp ((N : ℝ) * y)) ∂ν)) -
            Real.exp (-(T / (N : ℝ) *
              (ν (Iio (0 : ℝ))).toReal))))) :
    c = 0 := by sorry
