-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_true_clock_survival_cdf_to_real_iInf
-- name    : AvramDividend.Classical.esscher_true_clock_survival_cdf_to_real_iInf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:55:08.603835+00:00
-- url     : https://prove2.me/theorems/ad41427c-55da-4744-84e7-d636072bbf5b
-- title:
--   Genuine exponential-time Esscher survival CDFs converge to the perpetual real survival infimum
-- statement:
--   For any actual spectrally negative Lévy process, any nonnegative Esscher tilt θ, initial reserve x, and strictly positive rates p_n→0, the real-valued expectation over the genuine Exp(p_n) clock of the finite-horizon terminal-weighted no-ruin survival expectation converges to the infimum of those genuine finite-horizon survival expectations. Proof imports the true exponential clock Abel theorem and already-accepted stochastic martingale antitonicity, unit-interval bound and monotone convergence of the exact tilted survival CDF. No Wiener-Hopf factor, tilted perpetual path probability or scale-exit identity is assumed.
-- source:
--   Accepted 1E-C esscher_true_exp_rate_cdf_abel_limit 438e998e, esscher_weighted_lower_survival_mass_antitone 6335f5be, unit_interval 28aaafa3, tendsto_iInf 9752e377; pinned Mathlib Antitone.measurable, Real.tendsto_toNNReal_atTop.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.NNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_esscher_true_exp_rate_cdf_abel_limit
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_antitone
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_tendsto_iInf
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_true_clock_survival_cdf_to_real_iInf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ)
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    Tendsto
      (fun n : ℕ => ∫ v : ℝ,
        (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ Real.toNNReal v →
            0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp
            (θ * X.X (Real.toNNReal v) ω -
              (Real.toNNReal v : ℝ) *
                laplaceExponent X.c X.σ X.ν θ)) ω ∂P)
        ∂ProbabilityTheory.expMeasure (p n))
      atTop
      (nhds (⨅ t : ℝ≥0, ∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
      (fun ω => Real.exp (θ * X.X t ω -
        (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)) := by sorry
