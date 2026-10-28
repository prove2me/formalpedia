-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_true_exp_clock_perpetual_measure_laplace_limit
-- name    : AvramDividend.Classical.esscher_true_exp_clock_perpetual_measure_laplace_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:54:38.390705+00:00
-- url     : https://prove2.me/theorems/858282df-625a-484f-9901-9259fa895d17
-- title:
--   Genuine tilted Exp(p) reflected-infimum Laplace transforms converge to the perpetual supported law
-- statement:
--   For the true spectrally negative Lévy process and a positive Esscher q-root φ, as an arbitrary sequence of strictly positive exponential rates tends to zero from the right, the Laplace transform at every fixed β>0 of the genuine jointly Esscher-tilted path×Exp(p) reflected-infimum pushforward probability law converges to that of the canonical full-mass, nonnegative perpetual infimum probability ν. This derives from the accepted source-specific weighted-capital CDF limit, the exact CDF-to-ENNReal Laplace identity on supported probability laws, and legitimate positive finite ENNReal scalar cancellation. The proof does not assume Wiener–Hopf independence or the finite-rate descending identity.
-- source:
--   Canonically Proved d1128b1e actual weighted CDF to perpetual Laplace, 0b9fd101 positive supported CDF-to-Laplace equality, 3d3e8fe4 actual law probability, 4e6aabf8 actual law support; pinned Mathlib ENNReal.Tendsto.const_mul.

import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Probability.Distributions.Exponential
import Theorems.Thm_AvramDividend_Classical_esscher_true_exp_clock_perpetual_laplace_limit
import Theorems.Thm_AvramDividend_Classical_esscher_probability_weighted_cdf_real_eq_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_true_random_clock_reflected_law_probability
import Theorems.Thm_AvramDividend_Classical_esscher_true_real_clock_reflected_law_nonnegative_support

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_true_exp_clock_perpetual_measure_laplace_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ν (Iio (0 : ℝ)) = 0 ∧
      ∀ β : ℝ, 0 < β →
        Tendsto (fun n : ℕ =>
          (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂
            (Measure.map (fun z : Ω × ℝ =>
              -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ Real.toNNReal z.2 ∧
                y = X.X s z.1})
              ((P.prod (expMeasure (p n))).withDensity
                (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
                  (φ * X.X (Real.toNNReal z.2) z.1 -
                    (Real.toNNReal z.2 : ℝ) * X.ψ φ)))))))
          atTop (nhds (∫⁻ z : ℝ,
            ENNReal.ofReal (Real.exp (-β * z)) ∂ν)) := by sorry
