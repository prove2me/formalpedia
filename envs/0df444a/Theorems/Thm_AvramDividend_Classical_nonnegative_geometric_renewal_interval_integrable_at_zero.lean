-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_geometric_renewal_interval_integrable_at_zero
-- name    : AvramDividend.Classical.nonnegative_geometric_renewal_interval_integrable_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:15:41.212992+00:00
-- url     : https://prove2.me/theorems/bc189504-775f-40a5-8cb3-005af48d3f89
-- title:
--   Zero-endpoint interval integrability of nonnegative geometric renewal-power series
-- statement:
--   A renewal-power series of nonnegative functions with summable pointwise terms and geometrically bounded positive-axis integrated masses is interval-integrable from zero to every positive endpoint. This closes the at-zero integrability step needed in the bounded-variation Esscher renewal-density representation, provided the causal powers admit the stated global positivity and summability hypotheses.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals

open MeasureTheory Set

theorem AvramDividend.Classical.nonnegative_geometric_renewal_interval_integrable_at_zero
    (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hpoint : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), F n x ∂volume) ≤ ρ ^ (n + 1)) :
    ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun y : ℝ => ∑' n : ℕ, F n y) volume 0 x := by sorry
