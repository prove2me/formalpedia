-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_exp_clock_supremum_full_law_ws01d
-- name    : AvramDividend.Classical.esscher_positive_root_exp_clock_supremum_full_law_ws01d
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:05:28.115996+00:00
-- url     : https://prove2.me/theorems/cf4dc156-a2f9-41cc-85ef-d6492b918ccf
-- title:
--   Full exponential law of genuine random-terminal Esscher-tilted Lévy running supremum
-- statement:
--   For spectrally negative Lévy X under P, φ>0 with ψ(φ)=q>0, an independent genuine real E~Exp(p) with p>0, and λ>0 satisfying ψ(φ+λ)-q=p, the pushforward of the true Esscher terminal joint probability (P⊗Exp(p)).withDensity exp(φX_E-qE) through the actual running supremum over [0,E] equals the real exponential distribution expMeasure λ. This includes its zero atom and support, and follows from the Proved exact tilted strict tail with probability normalisation and Borel-law extension, without WH independence, fixed-terminal Q_T or two-sided exit.
-- source:
--   Kuznetsov–Kyprianou–Rivero 2012 Section 2.1 and 2.5; canonically Proved tilted true-clock strict upper-tail theorem 0e6d186f-abc0-4a83-9008-29e1b432641a, real-clock likelihood measurability de339769-89f8-41e1-8523-7683a2f71178, true joint Esscher probability 146b0027-8594-4660-b77c-47dd12219a9b, genuine real expMeasure tail 69bfdea1-9b67-42db-ab4b-e2473b94061f, and established original P supremum full-law pattern 8ecbee20-1cc1-4009-989a-759f94ded31e.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_exp_clock_supremum_tail_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_positive_root_exp_clock_supremum_full_law_ws01d
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (phi q : ℝ) (hphi : 0 < phi) (hq : 0 < q) (hroot : X.ψ phi = q)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam)
    (hshift : X.ψ (phi + lam) - q = p) :
    Measure.map (fun z : Ω × ℝ => runningSup X z.2.toNNReal z.1)
      ((P.prod (ProbabilityTheory.expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (phi * X.X z.2.toNNReal z.1 - (z.2.toNNReal : ℝ) * q)))) =
    ProbabilityTheory.expMeasure lam := by sorry
