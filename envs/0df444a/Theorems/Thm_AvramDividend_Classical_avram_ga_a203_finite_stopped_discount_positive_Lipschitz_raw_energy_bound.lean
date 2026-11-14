-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a203_finite_stopped_discount_positive_Lipschitz_raw_energy_bound
-- name    : AvramDividend.Classical.avram_ga_a203_finite_stopped_discount_positive_Lipschitz_raw_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:34:31.406894+00:00
-- url     : https://prove2.me/theorems/c1364352-4c80-403d-8921-9834eed75846
-- title:
--   Finite stopped Gaussian source positive discount mismatch is bounded by discount width times Lipschitz constant times raw first energy
-- statement:
--   On any physical finite stopped grid with selected active cells, if each exponential discount factor difference lies between minus the common discount-step bound and zero, and the original source spatial value increment is Lipschitz with constant L times the raw source increment, then the positive part of the entire stopped discounted mismatch is bounded by q times the grid width times L times the finite stopped raw first absolute energy sum. This is the exact pointwise ingredient for a new mathematically sound source-specific discount L1 reduction, combining the Proved original Gaussian raw Cauchy bound a154 and discount-width square-energy a155 while avoiding the excessive generality in a151.
-- source:
--   Monotonicity of exponential discount, uniform Lipschitz pointwise bound, finite sum domination; actual stopped raw Gaussian source to be instantiated.

import Mathlib
open Real
noncomputable section

theorem AvramDividend.Classical.avram_ga_a203_finite_stopped_discount_positive_Lipschitz_raw_energy_bound
    (S : Finset ℕ) (A : ℕ → Prop) [DecidablePred A]
    (a u v R : ℕ → ℝ)
    (q Δ L : ℝ) (hq : 0 ≤ q) (hΔ : 0 ≤ Δ) (hL : 0 ≤ L)
    (hDisc : ∀ i ∈ S, -(q * Δ) ≤ a i ∧ a i ≤ 0)
    (hLip : ∀ i ∈ S, |u i - v i| ≤ L * |R i|) :
    max (∑ i ∈ S, if A i then a i * (u i - v i) else 0) 0 ≤
      q * Δ * L * (∑ i ∈ S, if A i then |R i| else 0) := by sorry
