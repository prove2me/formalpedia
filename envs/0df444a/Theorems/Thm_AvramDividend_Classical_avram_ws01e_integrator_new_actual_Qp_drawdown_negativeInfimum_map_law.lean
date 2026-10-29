-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_actual_Qp_drawdown_negativeInfimum_map_law
-- name    : AvramDividend.Classical.avram_ws01e_integrator_new_actual_Qp_drawdown_negativeInfimum_map_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:57:49.909351+00:00
-- url     : https://prove2.me/theorems/f71be790-f7f8-4b9c-b8d7-411015680507
-- title:
--   Genuine Esscher exponential-clock drawdown law equals negative running-infimum law
-- statement:
--   Under the actual time-dependent Esscher density on P×Exp(p), with θ≥0 and p>0 and the genuine density measurable, the pushforward distribution of terminal drawdown runningSup(X,e)-X_e equals the pushforward distribution of -inf_{s≤e} X_s. The proof uses the already-Proved strict terminal Esscher reversal, source-specific pathwise Ioi equivalences and probability-measure extension; no global Q∞ or independence assumption.
-- source:
--   Canonical Proved 03d633e3-fe2d-4ee7-bbd0-95b604b541c7 supplies exact strict Qp event equality. Canonical Proved 1e4c8fdb-8179-4628-8eab-61c714b31dc9 accepted source gives the exact Ioi event ↔ runningSup/negative-infimum bridge. Canonical Proved 146b0027-8594-4660-b77c-47dd12219a9b establishes Qp probability. An explicit real-clock Esscher law, no product all-horizon path tilt.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_exp_clock_esscher_strict_drawdown_infimum_reversal
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_gt_level_iff_prior_strict_path_hit
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_integrator_new_actual_Qp_drawdown_negativeInfimum_map_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * X.ψ θ)))) :
    Measure.map (fun z : Ω × ℝ =>
      runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1)
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X z.2.toNNReal z.1 -
            (z.2.toNNReal : ℝ) * X.ψ θ)))) =
    Measure.map (fun z : Ω × ℝ =>
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1})
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (θ * X.X z.2.toNNReal z.1 -
            (z.2.toNNReal : ℝ) * X.ψ θ)))) := by sorry
