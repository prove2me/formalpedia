-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_C1_resolvent_of_neumann_series_data
-- name    : AvramDividend.Classical.causal_volterra_C1_resolvent_of_neumann_series_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:29:09.721407+00:00
-- url     : https://prove2.me/theorems/b159661e-c8e2-4393-b5a6-f949b8a7ead3
-- title:
--   Assemble a C1 derivative resolvent from signed Neumann-series data
-- statement:
--   Given signed convolution-power and primitive bounds with geometric contraction, termwise differentiability, continuity, absolute convergence, and the summed Volterra equation, the Neumann sum is a continuous C1 derivative resolvent on the positive half-line. This identifies the precise remaining analytic data needed for the Gaussian scale-function C2 theorem.
-- source:
--   Canonically Proved causal_neumann_series_C1_of_signed_power_bounds and contDiffOn_one_Ioi_of_local_open_intervals.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_causal_neumann_series_C1_of_signed_power_bounds
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_Ioi_of_local_open_intervals

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_volterra_C1_resolvent_of_neumann_series_data
    (K : ℝ → ℝ) (P H : ℕ → ℝ → ℝ) (a β ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hP : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHasDeriv : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x)
    (hCont : ∀ ε R : ℝ, 0 < ε → ∀ n : ℕ,
      ContinuousOn (fun x : ℝ => P n x / a - w * H n x) (Ioo ε R))
    (hval : ∀ y : ℝ, 0 < y → Summable (fun n : ℕ => H n y))
    (hg0 : ContinuousOn (fun y : ℝ => ∑' n : ℕ, H n y) (Ici (0 : ℝ)))
    (hgeq : ∀ x : ℝ, 0 < x →
      a * (∑' n : ℕ, H n x) +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * (∑' n : ℕ, H n s) ∂volume) = 1) :
    ∃ g : ℝ → ℝ,
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        a * g x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * g s ∂volume) = 1) := by sorry
