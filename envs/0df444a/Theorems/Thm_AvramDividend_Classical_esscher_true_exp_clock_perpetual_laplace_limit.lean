-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_true_exp_clock_perpetual_laplace_limit
-- name    : AvramDividend.Classical.esscher_true_exp_clock_perpetual_laplace_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T20:15:24.489669+00:00
-- url     : https://prove2.me/theorems/d1128b1e-7db5-47a6-a6ff-0768bb87adaa
-- title:
--   Actual positive-root exponential-clock Esscher capital-CDF transforms converge to the canonical perpetual Laplace transform
-- statement:
--   Given a true spectrally negative Lévy process, positive discount q, positive Esscher root φ satisfying ψ(φ)=q, and any vanishing sequence of strictly positive independent exponential clock rates p_n, construct a canonical perpetual nonnegative probability law ν. Then for every β>0, the ENNReal.ofReal of the real exponential capital-weighted CDF of the *genuine* rate-p_n random-time Esscher reflected-infimum pushforward law tends to (1/β) times the authentic Laplace transform of ν. The proof combines full-probability nonnegative support, source-specific exact random-clock CDF convergence, genuine pushforward probability, dominated convergence of probability CDF weighted integrals, and real-to-ENNReal cumulative-to-measure transform identity. It assumes no finite-rate Wiener-Hopf factor. The remaining factor is owned by 1E-B.
-- source:
--   Accepted source-specific CDF 58668a61, genuine law 3d3e8fe4, weighted CDF DCT 0bf634fd; source-specific perpetual support-laplace f370f2ab and real CDF-to-Laplace 0b9fd101 pending acceptance.

import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_probability_support_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_probability_weighted_cdf_real_eq_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_true_joint_clock_cdf_tendsto_perpetual
import Theorems.Thm_AvramDividend_Classical_esscher_true_random_clock_reflected_law_probability
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_esscher_probability_cdf_limits_imply_weighted_laplace_limits
open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_true_exp_clock_perpetual_laplace_limit
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
        Tendsto (fun n : ℕ => ENNReal.ofReal (∫ x in Ioi (0 : ℝ),
            Real.exp (-β * x) * cdf (Measure.map (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 ∧ y = X.X s z.1}) ((P.prod (expMeasure (p n))).withDensity (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (φ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ φ))))) x ∂volume))
          atTop (nhds (ENNReal.ofReal (1 / β) *
             (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-β * z)) ∂ν))) := by sorry
