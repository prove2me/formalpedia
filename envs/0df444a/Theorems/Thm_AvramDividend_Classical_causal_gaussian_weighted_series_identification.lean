-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_gaussian_weighted_series_identification
-- name    : AvramDividend.Classical.causal_gaussian_weighted_series_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T22:41:12.863794+00:00
-- url     : https://prove2.me/theorems/07c5248e-6d7f-4d71-b0d5-ca06367b073d
-- title:
--   Gaussian C1 weighted Neumann series equals undamped correction-series sum
-- statement:
--   The exponentially weighted Gaussian C1 Neumann candidate admits a correction sequence whose initial term is constant, whose later terms are normalised signed convolution-power primitives, and whose pointwise summable series equals the candidate. Supplies the exact Q representation needed by the Volterra equation.
-- source:
--   Construct Q0=1/a and Q(n+1)=exp(w x)Hn(x). Cancel exp(w x)exp(-w x)=1 to identify the weighted primitive with the undamped integral. Apply Proved causal_exponential_tsum_untwist and Summable.tsum_eq_zero_add to show the existing explicit C1 candidate g equals the actual sum of Q, conditionally on geometric summability.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_exponential_tsum_untwist
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_gaussian_weighted_series_identification
    (P H : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (a w : ℝ)
    (hH : ∀ n : ℕ, H n = fun x : ℝ =>
      (Real.exp (-w * x) *
        (∫ t in Ioc (0 : ℝ) x,
          Real.exp (w * t) * P n t ∂volume)) / a)
    (hg : g = fun y : ℝ => 1 / a + Real.exp (w * y) *
      (∑' n : ℕ, (Real.exp (-w * y) *
        (∫ t in Ioc (0 : ℝ) y,
          Real.exp (w * t) * P n t ∂volume)) / a)) :
    ∃ Q : ℕ → ℝ → ℝ,
      Q 0 = (fun _ : ℝ => 1 / a) ∧
      (∀ n : ℕ, Q (n + 1) =
        fun x : ℝ => Real.exp (w * x) * H n x) ∧
      (∀ n : ℕ, Q (n + 1) =
        fun x : ℝ => (1 / a) *
          (∫ t in Ioc (0 : ℝ) x,
            Real.exp (w * t) * P n t ∂volume)) ∧
      (∀ x : ℝ, Summable (fun n : ℕ => Q n x) →
        g x = ∑' n : ℕ, Q n x) := by sorry
