-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_initial_payoff
-- name    : AvramDividend.Classical.chat04_killed_scale_initial_payoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:54:16.679043+00:00
-- url     : https://prove2.me/theorems/29d9c0a6-6198-4b74-a3cf-5f5b32ce4c90
-- title:
--   At nonnegative initial reserve the killed discounted scale payoff starts at W(x)
-- statement:
--   A spectrally negative Lévy process starts at X_0=0. At initial time t=0 a nonnegative starting reserve x has survived the entire interval [0,0]; the discounted factor exp(-q*0)=1. Thus the correctly history-killed q-scale payoff at time zero equals W(x) pathwise. No Standing or martingale assumption is needed. This establishes initial normalization for the genuinely killed process.

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat04_killed_scale_initial_payoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (hx : 0 ≤ x) (W : ℝ → ℝ) :
    ∀ ω : Ω,
      ({ω | ∀ s : ℝ≥0, s ≤ (0 : ℝ≥0) → 0 ≤ x + X.X s ω}.indicator
        (fun ω => Real.exp (-(q * ((0 : ℝ≥0) : ℝ))) *
          W (x + X.X (0 : ℝ≥0) ω)) ω) = W x := by sorry
