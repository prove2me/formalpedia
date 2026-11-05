-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_discount_clock_grid_integral
-- name    : AvramDividend.Classical.avram_p3_main_public_discount_clock_grid_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:07:05.567775+00:00
-- url     : https://prove2.me/theorems/a5197460-0b3b-4cfb-b614-bc4b09a0f69c
-- title:
--   Public exact finite-grid BV negative discount q-clock integral identity
-- statement:
--   Public importable replay of the identical previously proved finite-grid discount product clock correction, preserving the exact negative q weighted exponential integral over actual successive nonnegative times.
-- source:
--   Previously accepted private source AvramDividend.Classical.avram_p3_d_bvmesh_discount_clock_finite_grid_integral, UUID d1044e44-3cab-4ed0-b8cf-e8e745a05b76, submission 65b29aaa-21a1-4e39-853a-60944310b97f, exact proof source SHA-256 f4e3adf43c4992c910fd1c7f4d8f10940000fcc2d10208dd18021452b5eec124; source-specific original BV P3 a19d8b28.

import Mathlib
open MeasureTheory
open scoped BigOperators NNReal

theorem AvramDividend.Classical.avram_p3_main_public_discount_clock_grid_integral
    (n : ℕ) (u : ℕ → ℝ≥0) (post : ℕ → ℝ) (q : ℝ) :
    (∑ i ∈ Finset.range n,
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) * post (i + 1)) =
    ∑ i ∈ Finset.range n,
      (∫ t in (u i : ℝ)..(u (i + 1) : ℝ),
        -(q * Real.exp (-(q * t)))) * post (i + 1) := by sorry
