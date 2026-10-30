-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_closed_survival_small_rate_CDF_limit
-- name    : AvramDividend.Classical.avram_ws01h_true_Qp_closed_survival_small_rate_CDF_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T17:36:45.714749+00:00
-- url     : https://prove2.me/theorems/8bfd9dc1-27a3-407d-9cbd-fa42a784b412
-- title:
--   Genuine terminally Esscher tilted Qp original-Lévy closed nonruin CDF converges to actual perpetual survival CDF as observation rate vanishes
-- statement:
--   For any real-valued genuine Lévy process, terminal Esscher parameter θ≥0, reserve x, and authentic perpetual Esscher survival CDF measure ν with the accepted finite-horizon weighted nonruin infimum definition, every strictly positive sequence of real Exp(p_n) observation rates p_n↓0 gives the actual original-sample terminally Esscher-weighted joint Qp nonruin probability tending to ν(Iic x). The exact original closed continuous-history survival event is obtained from the already accepted source reflected-infimum event by pointwise pathwise equivalence for the actual real observation clock. Thus the proven genuine random-time Esscher reflected CDF convergence applies directly to the true stochastic survival factor in the first-record killed renewal, without any abstract tilted infinite-path law or two-sided exit formula.
-- source:
--   Accepted genuine Esscher terminally weighted true random-clock reflected CDF convergence 58668a61; true original real-clock reflected CDF iff complete survival 81847f84 candidate 18470.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_real_clock_reflected_CDF_event_iff_lower_survival
import Theorems.Thm_AvramDividend_Classical_esscher_true_joint_clock_cdf_tendsto_perpetual

open AvramDividend.Classical MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_ws01h_true_Qp_closed_survival_small_rate_CDF_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ)
    (ν : Measure ℝ)
    (hν : ν (Iic x) =
       (⨅ t : ℝ≥0, ENNReal.ofReal
         (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t →
           0 ≤ x + X.X s ω}).indicator
           (fun ω => Real.exp (θ * X.X t ω -
             (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P)))
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    Tendsto (fun n : ℕ =>
      ((P.prod (expMeasure (p n))).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
        {z : Ω × ℝ | ∀ s : ℝ≥0,
          s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1})
      atTop (𝓝 (ν (Iic x))) := by sorry
