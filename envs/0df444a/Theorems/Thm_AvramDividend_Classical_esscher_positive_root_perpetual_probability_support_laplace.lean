-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_probability_support_laplace
-- name    : AvramDividend.Classical.esscher_positive_root_perpetual_probability_support_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T20:04:09.456331+00:00
-- url     : https://prove2.me/theorems/f370f2ab-18c8-417f-8739-ff5d31dd12aa
-- title:
--   Canonical positive-root perpetual Esscher probability has nonnegative support and an exact cumulative-to-measure Laplace identity
-- statement:
--   For any genuine spectrally negative Lévy process, q>0 and positive Esscher root φ>0 satisfying ψ(φ)=q, construct one canonical perpetual reflected-infimum probability ν with support on [0,∞), exact all-threshold Esscher survival CDF, all-β>0 identity relating exponentially weighted cumulative ν CDF integrals to the Laplace transform of ν, and previously established nontrivial lower mass bound. The proof reconciles the independently established full-probability and finite nonnegative perpetual measures by uniqueness from all closed-half-line CDFs; there is no extra support assumption and no Wiener-Hopf scalar transform premise.
-- source:
--   Accepted full-mass canonical ν 70aae7c7, finite nonnegative ν bd0e0e7b, exact positiveLaplace_cumulative_measure 6027eb2c, Mathlib Measure.ext_of_Iic. No finite-rate Wiener–Hopf identity.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_positive_root_perpetual_infimum_probability_full_mass
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_perpetual_infimum_finite_nonnegative_distribution
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_positive_root_perpetual_probability_support_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q φ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ν (Iio (0 : ℝ)) = 0 ∧
      (∀ x : ℝ, ν (Iic x) =
        (⨅ t : ℝ≥0, ENNReal.ofReal
          (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
            (fun ω => Real.exp (φ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P))) ∧
      (∀ β : ℝ, 0 < β →
        (∫⁻ x : ℝ in Ioi 0,
     ENNReal.ofReal (Real.exp (-β * x)) * ν (Iic x)) =
          ENNReal.ofReal (1 / β) * (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν)) ∧
      (∀ b : ℝ, 0 < b →
        ENNReal.ofReal (1 - Real.exp (-(φ / 2) * b)) ≤
          ν (Iic b)) := by sorry
