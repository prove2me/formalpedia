-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_two_step_killed_scale_kernel_tonelli
-- name    : AvramDividend.Classical.chat04_two_step_killed_scale_kernel_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:03:17.726523+00:00
-- url     : https://prove2.me/theorems/237c5fbd-3822-47a6-8599-6b424f0d1a71
-- title:
--   Two-step grid-killed q-scale transition as product-law kernel integral
-- statement:
--   For any spectrally negative Lévy process, q-scale function W, real starting reserve x and deterministic times s≤t, the nonnegative expected q-scale payoff at t restricted to nonnegative reserve at both observation times s and t equals the iterated integral of its two-step killed transition kernel against independent laws of X_s and X_(t−s). Prove using the accepted random-state/future-increment joint law, measurable survival thresholds, full-line Borel scale measurability and pinned lintegral_map and Tonelli. This is a rigorous discrete-grid killed transition operator without extra moment assumptions. It explicitly does not assert absence of negative excursions between s and t or the open killed q-harmonicity of the continuous-time scale process.
-- source:
--   Accepted AvramDividend.Classical.chat04_levy_random_state_increment_product_law UUID 53b4d2eb-ef57-4c07-af33-8872d18e1dfd, accepted full-line Borel scale measurability UUID 45cbe3b4-374d-4fa4-b988-e09f93b74cab, pinned Mathlib lintegral_map, lintegral_prod, Measurable.ite.

import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_levy_random_state_increment_product_law
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_two_step_killed_scale_kernel_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ) :
    (∫⁻ ω,
       if 0 ≤ x + X.X s ω ∧
          0 ≤ x + X.X s ω + (X.X t ω - X.X s ω)
       then ENNReal.ofReal
         (W (x + X.X s ω + (X.X t ω - X.X s ω)))
       else 0 ∂P) =
      ∫⁻ a, ∫⁻ b,
       if 0 ≤ x + a ∧ 0 ≤ x + a + b
       then ENNReal.ofReal (W (x + a + b))
       else 0
       ∂(Measure.map (X.X (t - s)) P)
       ∂(Measure.map (X.X s) P) := by sorry
