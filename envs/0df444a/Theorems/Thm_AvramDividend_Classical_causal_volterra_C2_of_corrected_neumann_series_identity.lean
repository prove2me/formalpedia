-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_C2_of_corrected_neumann_series_identity
-- name    : AvramDividend.Classical.causal_volterra_C2_of_corrected_neumann_series_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:07:03.531331+00:00
-- url     : https://prove2.me/theorems/c09013fb-277a-4e66-9f59-a8989b8d1e54
-- title:
--   C2 Gaussian Volterra regularity from an exact corrected Neumann identity
-- statement:
--   For an integrated Gaussian Volterra solution V, signed Neumann corrections with quadratic-geometric derivative bounds yield C2 smoothness, provided their explicitly displayed 1/a-forced sum satisfies the exact second-kind Volterra resolvent equation. The remaining identity is a separate analytic kernel-power summation task and is an explicit hypothesis.
-- source:
--   Full-resolvent C1 regularity plus the canonically Proved causal_volterra_C2_of_C1_derivative_resolvent.

import Theorems.Thm_AvramDividend_Classical_causal_neumann_full_resolvent_regular_of_correction_bounds
import Theorems.Thm_AvramDividend_Classical_causal_volterra_C2_of_C1_derivative_resolvent

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_volterra_C2_of_corrected_neumann_series_identity
    (K V : ℝ → ℝ) (P H : ℕ → ℝ → ℝ) (a β ρ w : ℝ)
    (ha : 0 < a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw : 0 ≤ w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C)
    (hVe : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x)
    (hP : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      |P n x| ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (hH : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x →
      |H n x| ≤ ρ ^ (n + 1) / a)
    (hHcont : ∀ n : ℕ, ContinuousOn (H n) (Ici (0 : ℝ)))
    (hHasDeriv : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∀ x : ℝ, ε ≤ x →
      HasDerivAt (H n) (P n x / a - w * H n x) x)
    (hCont : ∀ ε R : ℝ, 0 < ε → ∀ n : ℕ,
      ContinuousOn (fun x : ℝ => P n x / a - w * H n x) (Ioo ε R))
    (hEq : ∀ x : ℝ, 0 < x →
      a * (1 / a + Real.exp (w * x) * (∑' n : ℕ, H n x)) +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) *
            (1 / a + Real.exp (w * s) *
              (∑' n : ℕ, H n s)) ∂volume) = 1) :
    ContDiffOn ℝ 2 V (Ioi (0 : ℝ)) := by sorry
