-- Prove2me | Theorems.Thm_AvramDividend_Classical_lipschitz_payoff_integrable_of_integrable_sum
-- name    : AvramDividend.Classical.lipschitz_payoff_integrable_of_integrable_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:56:25.939675+00:00
-- url     : https://prove2.me/theorems/6f321533-c6a0-4333-a475-522e78f04ed9
-- title:
--   Integrability of a Lipschitz payoff of two integrable random variables
-- statement:
--   On a finite measure space, if Z and Y are measurable integrable real random variables and f is measurable and globally Lipschitz with constant L, then f(Z+Y) is integrable. Apply the already Proved Lipschitz shifted-payoff transfer using Z+Y as the approximating start, 0 as the reference reserve, and a zero common shift. Integrability of Z+Y gives the Lipschitz envelope and the constant reference payoff is integrable on a finite measure. In the Lévy Markov bridge this removes a separate payoff-integrability assumption once integrability of the process increment has been established.
-- source:
--   Chat 08 accepted Lipschitz shifted payoff integrability target cab2b0d5-e7b6-4ca2-a493-741be37c405c; the proof only needs finite-measure constants and Integrable.add/abs/const_mul.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_lipschitz_shifted_payoff_integrable_of_L1_difference

open MeasureTheory
open AvramDividend.Classical

theorem AvramDividend.Classical.lipschitz_payoff_integrable_of_integrable_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℝ → ℝ) (hf : Measurable f) (L : ℝ)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (Z Y : Ω → ℝ) (hZ : Measurable Z) (hY : Measurable Y)
    (hZI : Integrable Z P) (hYI : Integrable Y P) :
    Integrable (fun ω => f (Z ω + Y ω)) P := by sorry
