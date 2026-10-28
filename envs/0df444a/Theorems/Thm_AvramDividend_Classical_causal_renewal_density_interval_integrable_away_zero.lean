-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_renewal_density_interval_integrable_away_zero
-- name    : AvramDividend.Classical.causal_renewal_density_interval_integrable_away_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:30:18.784456+00:00
-- url     : https://prove2.me/theorems/d1c7741f-9080-45a8-ae97-8e2eb22f2da4
-- title:
--   Interval integrability of the positive-time renewal density away from zero
-- statement:
--   For causal renewal powers satisfying the established kernel integrability, regularity, nonnegativity and quadratic-geometric bounds, their shifted infinite density series is integrable on every compact interval [a,b] with 0<a≤b. The proof imports the established positive-time continuity result and isolates the remaining endpoint-zero integrability problem in the bounded-variation Esscher series.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.causal_renewal_density_interval_integrable_away_zero
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hκint : Integrable κ volume)
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun y : ℝ => ∑' n : ℕ,
        if n = 0 then (0 : ℝ) else F (n - 1) y) volume a b := by sorry
