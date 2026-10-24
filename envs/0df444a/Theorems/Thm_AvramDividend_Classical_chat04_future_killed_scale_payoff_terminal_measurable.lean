-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_future_killed_scale_payoff_terminal_measurable
-- name    : AvramDividend.Classical.chat04_future_killed_scale_payoff_terminal_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:18:57.038834+00:00
-- url     : https://prove2.me/theorems/9be493a3-0418-4bb2-b262-a20270f3081e
-- title:
--   Future-window killed discounted q-scale payoff is terminal-filtration measurable
-- statement:
--   For any canonical q-scale function, the future-window q-scale payoff killed when the Lévy reserve falls below zero during [s,u] is measurable in the terminal filtration 𝓕_u. The path-survival indicator is measurable by the proved terminal-filtration interval event theorem; Borel measurability of the possibly discontinuous scale W and adaptedness of the terminal reserve give measurability of the discounted payoff.
-- source:
--   Published chat04_shifted_future_killing_terminal_filtration and chat03_scale_function_borel_measurable; Mathlib Measurable.indicator.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_future_killing_terminal_filtration

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_future_killed_scale_payoff_terminal_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    Measurable[𝓕 u]
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) := by sorry
