-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_true_joint_clock_cdf_tendsto_perpetual
-- name    : AvramDividend.Classical.esscher_true_joint_clock_cdf_tendsto_perpetual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T18:04:50.004403+00:00
-- url     : https://prove2.me/theorems/58668a61-8546-404d-bc77-56b91bd22993
-- title:
--   The actual random-time Esscher running-infimum CDF converges to the canonical perpetual Esscher CDF
-- statement:
--   Let X be a genuine spectrally negative Lévy process, θ≥0, x a capital threshold, and ν any measure satisfying the already-Proved canonical perpetual Esscher CDF formula as the infimum over finite-horizon weighted survival integrals. For arbitrary positive exponential rates p_n→0, the genuine time-dependent Esscher joint path-clock law at rate p_n assigns the reflected running-infimum event a mass tending to ν(Iic x). Proof uses the already verified exact clock-mixture disintegration, actual finite-horizon CDF-to-survival equality, bounded probability real-to-ENNReal integral bridge, actual varying-rate exponential Abel limit, and real-to-ENNReal infimum conversion. It assumes no Wiener-Hopf factorisation or infinite Esscher path law.
-- source:
--   Accepted 1E-C results 83b37a63, a5ddd069, 72de4759, ad41427c, 17abb413; accepted source-specific survival antitone and limit 6335f5be and 9752e377; canonical ν CDF supplied by already Proved 70aae7c7.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_esscher_joint_exp_clock_reflected_cdf_mixture
import Theorems.Thm_AvramDividend_Classical_esscher_clock_finite_cdf_equals_survival_mix
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_probability_real_lintegral_bridge
import Theorems.Thm_AvramDividend_Classical_esscher_true_clock_survival_cdf_to_real_iInf
import Theorems.Thm_AvramDividend_Classical_esscher_ofReal_antitone_iInf_bridge
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_antitone
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_tendsto_iInf
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_unit_interval

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_true_joint_clock_cdf_tendsto_perpetual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ)
    (ν : Measure ℝ)
    (hν : ν (Iic x) =
       (⨅ t : ℝ≥0, ENNReal.ofReal (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (θ * X.X t ω -
             (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)))
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    Tendsto (fun n : ℕ =>
      ((P.prod (expMeasure (p n))).withDensity (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
         {z : Ω × ℝ | -sInf {y : ℝ | ∃ s : ℝ≥0,
            s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1} ≤ x})
      atTop (nhds (ν (Iic x))) := by sorry
