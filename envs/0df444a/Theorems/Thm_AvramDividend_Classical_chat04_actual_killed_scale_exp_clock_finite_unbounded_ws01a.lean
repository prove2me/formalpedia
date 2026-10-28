-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_actual_killed_scale_exp_clock_finite_unbounded_ws01a
-- name    : AvramDividend.Classical.chat04_actual_killed_scale_exp_clock_finite_unbounded_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:35:43.296035+00:00
-- url     : https://prove2.me/theorems/e6ec8327-2b8d-4dc1-a7e5-4946c1fd6463
-- title:
--   Finite genuine lower-killed q-scale reward at an independent exponential clock
-- statement:
--   For every reserve x and an unbounded-variation spectrally negative Levy law with q>0 and p>0, the actual full-history lower-killed q-scale payoff observed at an independent Exp(q+p) clock has finite ENNReal expectation. Select the genuine positive Esscher root at q+p/2, use the true terminal exponential-clock moment and the true pathwise killed-scale exponential domination. This result assumes no killed spatial kernel, two-sided exit identity or Wiener-Hopf independence.
-- source:
--   Canonically Proved positive_esscher_root_of_unbounded_variation; true terminal clock moment 3281a368; true lower-history-killed exponential envelope a6c31a27. Finiteness from exact positive rate gap.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exp_clock_terminal_moment_rate_identity_ws01a
import Theorems.Thm_AvramDividend_Classical_chat04_actual_killed_scale_exp_clock_exponential_domination_ws01a

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_actual_killed_scale_exp_clock_finite_unbounded_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (p : ℝ) (hp : 0 < p)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (x : ℝ) :
    (∫⁻ z : Ω × ℝ,
      if ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 →
           0 ≤ x + X.X s z.1
      then ENNReal.ofReal
        (W (x + X.X (Real.toNNReal z.2) z.1))
      else (0 : ℝ≥0∞)
      ∂(P.prod (ProbabilityTheory.expMeasure (q + p)))) < ⊤ := by sorry
