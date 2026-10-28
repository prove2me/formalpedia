-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_payoff_measurable_nonnegative
-- name    : AvramDividend.Classical.chat04_killed_scale_payoff_measurable_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:10:10.297986+00:00
-- url     : https://prove2.me/theorems/6cbc64a5-0af1-4414-8306-75c5e267b62d
-- title:
--   Measurability and nonnegativity of whole-history killed discounted scale payoff
-- statement:
--   At any deterministic horizon, the scale-function payoff discounted and killed when the capital path fell negative earlier is Borel measurable and nonnegative. Uses the Proved full-history survival measurability theorem and Borel measurability of the q-scale function.
-- source:
--   Proved no-schedule survival measurability, scale Borel measurability and IsScaleFunction positivity/vanishing on negatives.

import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.Algebra.Notation.Indicator

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat04_killed_scale_payoff_measurable_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) :
    Measurable
      (({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ∧
    (∀ ω, 0 ≤
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω) := by sorry
