-- Prove2me | solution 1 for eq30RightSlope_tendsto_atTop_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:40:40.135761+00:00
-- url     : https://prove2.me/submissions/063b4a3e-e053-40b6-b8f2-a860344e8889

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_eq30RightSlope
import Definitions.Def_eq30SlopeThreshold
import Theorems.Thm_eq30RightSlope_eq_zero_of_threshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open NestedSeatAlloc.IntPolicy
open Filter
open scoped Topology

theorem eq30RightSlope_tendsto_atTop_zero
    (f p x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (k : ℕ) :
    Tendsto (fun n : ℕ => eq30RightSlope f p x k (n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (eq30SlopeThreshold p x k)] with n hn
  exact (eq30RightSlope_eq_zero_of_threshold f p x hx k n hn).symm

theorem solution
    (f p x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) (k : ℕ) :
    Tendsto (fun n : ℕ => eq30RightSlope f p x k (n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (eq30SlopeThreshold p x k)] with n hn
  exact (eq30RightSlope_eq_zero_of_threshold f p x hx k n hn).symm


