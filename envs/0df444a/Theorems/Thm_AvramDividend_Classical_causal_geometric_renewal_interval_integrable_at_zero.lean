-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_geometric_renewal_interval_integrable_at_zero
-- name    : AvramDividend.Classical.causal_geometric_renewal_interval_integrable_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:18:31.73557+00:00
-- url     : https://prove2.me/theorems/1f5841f8-4e23-4872-8e71-1dac76606424
-- title:
--   At-zero integrability of geometrically bounded causal renewal densities
-- statement:
--   For a causal family of real convolution powers vanishing at nonpositive times, geometric bounds on the positive-axis integrated masses, positive-time nonnegativity and positive-time pointwise convergence suffice to make the summed density interval-integrable from zero to every positive endpoint. This removes unnecessary global hypotheses from the geometric renewal integrability theorem and supplies the exact zero-boundary property needed by the Esscher scale-density representation.

import Theorems.Thm_AvramDividend_Classical_nonnegative_geometric_renewal_interval_integrable_at_zero

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_geometric_renewal_interval_integrable_at_zero
    (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ F n x)
    (hpoint : ∀ x : ℝ, 0 < x →
      Summable (fun n : ℕ => F n x))
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), F n x ∂volume) ≤ ρ ^ (n + 1)) :
    ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun y : ℝ => ∑' n : ℕ, F n y) volume 0 x := by sorry
