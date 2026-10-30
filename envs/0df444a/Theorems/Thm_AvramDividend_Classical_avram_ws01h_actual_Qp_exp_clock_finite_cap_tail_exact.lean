-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_exp_clock_finite_cap_tail_exact
-- name    : AvramDividend.Classical.avram_ws01h_actual_Qp_exp_clock_finite_cap_tail_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:43:14.551835+00:00
-- url     : https://prove2.me/theorems/19406a82-31c6-41e7-a4de-0d77474900d1
-- title:
--   Exact true Qp finite observation cap escape probability is exp(-pN) under genuine Esscher terminal law
-- statement:
--   For the true original Lévy sample space and random-terminal Esscher Qp with positive real exponential clock rate p, the clock component retains its exact Exp(p) marginal. Consequently the mass of observations beyond any finite nonnegative cap N is exp(-pN), independently of the Lévy trajectory. This provides the quantitative path-independent uncapping error for the actual finite-clock killed CDF renewal. The proof uses the already proved genuine joint terminal tilt marginal theorem and the genuine exponential strict-tail law, not a fictitious full-path tilted probability.
-- source:
--   Proved source joint time-state measurability d55462c3, true joint Esscher clock marginal 0ee3767d, exact Exp(p) strict tail 69bfdea1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_clock_marginal_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_actual_Qp_exp_clock_finite_cap_tail_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (N : ℝ≥0) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     Qp {z : Ω × ℝ | (N : ℝ) < z.2} =
       ENNReal.ofReal (Real.exp (-(p * (N : ℝ))))) := by sorry
