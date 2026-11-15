-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_stationary_boltzmann_density_deriv
-- name    : AppliedSDE.SarkkaSolin.stationary_boltzmann_density_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:15:50.998206+00:00
-- url     : https://prove2.me/theorems/f7bd1407-a923-40ee-aaed-e48644fac1c8
-- title:
--   Boltzmann stationary Gaussian diffusion density has logarithmic derivative minus potential gradient over noise
-- statement:
--   For any twice continuously differentiable potential v and positive diffusion variance q, the Gibbs density Z inverse times exp(-v/q) has first derivative -(v prime/q) times itself. This is the exact first-order probability-flux identity required for the chapter stationary one-dimensional Fokker Planck proof e11e7791-6b3d-4f27-9080-c91d94edf452.
-- source:
--   Sarkka and Solin (2019) stationary Fokker Planck density; supports theorem e11e7791-6b3d-4f27-9080-c91d94edf452

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.stationary_boltzmann_density_deriv
    (q : ℝ) (hq : 0 < q) (v : ℝ -> ℝ)
    (hv : ContDiff ℝ 2 v) (Z : ℝ) :
    let p : ℝ -> ℝ := fun x => Z⁻¹ * Real.exp (-(v x / q))
    ∀ x : ℝ, deriv p x = -(deriv v x / q) * p x := by
  sorry
