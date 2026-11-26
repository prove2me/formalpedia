-- Prove2me | Theorems.Thm_BranchActualQ_dyadic_pointwise_tests_of_dominant_window
-- name    : BranchActualQ.dyadic_pointwise_tests_of_dominant_window
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-20T11:22:22.753177+00:00
-- url     : https://prove2.me/theorems/e9de5e0a-dc5a-4416-b206-ea60a6156dea
-- title:
--   Pointwise dyadic recurrence tests from a dominant oscillatory window
-- statement:
--   Assume a real family has nonnegative dyadic values under R and, under its negation, admits every sufficiently small positive phase of a dominant cosine with positive mass and vanishing normalized error. Then R is equivalent both to pointwise arbitrarily late nonnegative dyadic values and to pointwise arbitrarily late lower bounds D(2k) ≥ -ε D(k)^2 for every ε>0 on dyadic k.
-- source:
--   Projeto Desenvolvimento RH, Ricardo Marangoni Brandão Bueno, ataque à diagonal diádica de 20/11/2026, a partir da PF28 §166.

import Mathlib

theorem BranchActualQ.dyadic_pointwise_tests_of_dominant_window {X : Type*} (D : X → ℕ → ℝ) (R : Prop)
    (onLine : R → ∀ x j, 0 ≤ D x (2^j))
    (offLine : ¬ R → ∃ η : ℝ, 0 < η ∧ ∀ θ : ℝ, 0 < θ → θ < η →
      ∃ (x : X) (r mass : ℝ), 0 < r ∧ 0 < mass ∧
        Filter.Tendsto (fun k : ℕ => D x k / r^k - mass * Real.cos ((k : ℝ)*θ))
          Filter.atTop (nhds 0)) :
    (R ↔ ∀ x J, ∃ j ≥ J, 0 ≤ D x (2^j)) ∧
    (R ↔ ∀ x (ε : ℝ), 0 < ε → ∀ N : ℕ, ∃ j ≥ N,
      -(ε * (D x (2^j))^2) ≤ D x (2^(j+1))) := by sorry
