-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_geometric_weighted_tsum_integrable
-- name    : AvramDividend.Classical.causal_geometric_weighted_tsum_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T07:28:39.47978+00:00
-- url     : https://prove2.me/theorems/62825306-13c0-43d9-85ec-0b2e869690f7
-- title:
--   Weighted integrability of the nonnegative geometric renewal series
-- statement:
--   For nonnegative renewal-power functions whose exponentially weighted terms are integrable, converge pointwise and have geometric positive-half-line masses rho^(n+1) with 0<=rho<1, the exponentially weighted pointwise sum is integrable on the positive half-line. This supplies the separate IntegrableOn clause needed when constructing a positive-discount scale function from a zero-discount Neumann series.
-- source:
--   The proved nonnegative_integrable_tsum_of_summable_integrals theorem and the geometric-series summability lemma.

import Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals
import Mathlib.Analysis.SpecificLimits.Basic
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_geometric_weighted_tsum_integrable
    (F : ℕ → ℝ → ℝ) (θ ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * F n x)
      (Ioi (0 : ℝ)) volume)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hpoint : ∀ x : ℝ,
      Summable (fun n : ℕ => Real.exp (-(θ * x)) * F n x))
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * F n x ∂volume) =
        ρ ^ (n + 1)) :
    IntegrableOn
      (fun x : ℝ => ∑' n : ℕ, Real.exp (-(θ * x)) * F n x)
      (Ioi (0 : ℝ)) volume := by sorry
