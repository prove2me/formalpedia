-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_actual_Qp_all_borel_nonnegative_reward_factor
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_actual_Qp_all_borel_nonnegative_reward_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:08:24.6144+00:00
-- url     : https://prove2.me/theorems/fdae8fcf-2d0c-4c1d-8f0a-17dc05550e8e
-- title:
--   Genuine Esscher-clock supremum and drawdown factor all nonnegative Borel rewards
-- statement:
--   For every source spectrally negative Lévy process with genuinely measurable random-terminal Esscher density Qp, nonnegative tilt, positive exponential clock rate, and all nonnegative measurable rewards f,g on real supremum and drawdown values, the joint Qp lintegral of f(S)g(D) equals the product of the two Qp lintegrals. No boundedness or moment assumption on f,g, no independent path-clock tilt, and no conditional stochastic factorisation hypothesis is added. This is the all-Borel reward consequence of the accepted unconditional actual-Qp IndepFun theorem 421ab102.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_actual_Qp_all_borel_nonnegative_reward_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    let Qp : Measure (Ω × ℝ) :=
      (P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    (∫⁻ z, f (S z) * g (D z) ∂Qp) =
      (∫⁻ z, f (S z) ∂Qp) * (∫⁻ z, g (D z) ∂Qp) := by sorry
