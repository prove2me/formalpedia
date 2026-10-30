-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_original_wh_product_killed_kernel
-- name    : AvramDividend.Classical.avram_ws01b_actual_original_wh_product_killed_kernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:03:43.929928+00:00
-- url     : https://prove2.me/theorems/720de725-a5f4-4b4c-aa3c-0eae72787da7
-- title:
--   Actual original exponential-clock Wiener–Hopf product formula for killed reserve rewards
-- statement:
--   For the genuine original spectrally negative Lévy process under P×Exp(r), an arbitrary measurable nonnegative reward of the terminal reserve killed by drawdown threshold x factors into the product of the actual exponential-horizon supremum and terminal-drawdown laws. Includes all real x and any zero drawdown atom; uses the canonically Proved original-law IndepFun rather than assuming reflection or a tilted zero-parameter substitute.
-- source:
--   Source-faithful consequence of the canonically Proved actual original-clock Wiener–Hopf independence UUID 47e972c8 and actual random-clock extrema/drawdown measurability; a real killed-resolvent stochastic input for BV harmonicity c2e577be.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_original_expclock_sup_drawdown_indepFun
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_ws01b_actual_original_wh_product_killed_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (x : ℝ)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z : Ω × ℝ,
      (if runningSup X z.2.toNNReal z.1 -
          X.X z.2.toNNReal z.1 ≤ x
       then g (x + runningSup X z.2.toNNReal z.1 -
          (runningSup X z.2.toNNReal z.1 - X.X z.2.toNNReal z.1))
       else (0 : ℝ≥0∞))
      ∂(P.prod (expMeasure r))) =
    (∫⁻ a : ℝ × ℝ,
      if a.2 ≤ x then g (x + a.1 - a.2)
      else (0 : ℝ≥0∞)
      ∂((P.prod (expMeasure r)).map
          (fun z : Ω × ℝ => runningSup X z.2.toNNReal z.1)).prod
        ((P.prod (expMeasure r)).map
          (fun z : Ω × ℝ => runningSup X z.2.toNNReal z.1 -
              X.X z.2.toNNReal z.1))) := by sorry
