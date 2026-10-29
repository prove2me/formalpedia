-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_actual_Qp_joint_sup_drawdown_product_law
-- name    : AvramDividend.Classical.avram_ws01e_bt_new_actual_Qp_joint_sup_drawdown_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:06:45.16157+00:00
-- url     : https://prove2.me/theorems/2fbb60e0-a397-48b1-b83e-401f6ce24c22
-- title:
--   Actual Esscher exponential-clock supremum and drawdown have the product of their marginal laws
-- statement:
--   For the genuine spectrally negative Lévy process and its random-terminal Esscher density Qp, assuming only a nonnegative tilt, positive exponential rate, and measurable joint density, the pushed-forward joint law of the running supremum and terminal drawdown equals the product of their separate Qp marginal laws. All Borel product-test and nonnegative measurable reward identities follow. The proof uses the accepted unconditional Qp independence result and actual Qp normalisation and measurability; no independent tilted path-clock assumption is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bt_new_actual_Qp_joint_sup_drawdown_product_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    let Qp : Measure (Ω × ℝ) :=
      (P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
    let S : Ω × ℝ → ℝ :=
      fun z => runningSup X (Real.toNNReal z.2) z.1
    let D : Ω × ℝ → ℝ :=
      fun z => S z - X.X (Real.toNNReal z.2) z.1
    Measure.map (fun z => (S z, D z)) Qp =
      (Measure.map S Qp).prod (Measure.map D Qp) := by sorry
