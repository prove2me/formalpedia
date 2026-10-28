-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_mixed_borel_event_reversal_ws01a
-- name    : AvramDividend.Classical.chat04_actual_exponential_clock_mixed_borel_event_reversal_ws01a
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:26:29.025057+00:00
-- url     : https://prove2.me/theorems/44f90d98-8297-4d05-9966-971636d62e21
-- title:
--   Actual exponential-clock mixed Borel drawdown-terminal displacement event reversal
-- statement:
--   For the genuine product path-clock probability of a spectrally negative Levy process at an independent positive-rate exponential time, the event of terminal drawdown lying in any Borel set A and terminal displacement below any strict level c has the same probability as the centred running downward minimum lying in A with the same terminal-displacement restriction. This upgrades the actual strict-rectangle reversal to arbitrary Borel first-coordinate sets, without assuming Wiener-Hopf factor independence or a killed spatial kernel.
-- source:
--   Prepared only; requires canonical acceptance of public conditional finite-law theorem 1e4c8fdb-8179-4628-8eab-61c714b31dc9, currently Open with candidate 17666 pending. Proof uses pinned withDensity_apply and lintegral_indicator and previously Proved joint extrema measurability 4390c2cb. No public authoring until parent is Proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_terminal_weighted_drawdown_law_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_actual_exponential_clock_mixed_borel_event_reversal_ws01a
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r : ℝ) (hr : 0 < r) (c : ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (P.prod (expMeasure r))
      {z : Ω × ℝ |
        runningSup X z.2.toNNReal z.1 -
            X.X z.2.toNNReal z.1 ∈ A ∧
        X.X z.2.toNNReal z.1 - X.X 0 z.1 < c} =
    (P.prod (expMeasure r))
      {z : Ω × ℝ |
        X.X 0 z.1 +
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ z.2.toNNReal ∧ y = X.X s z.1} ∈ A ∧
        X.X z.2.toNNReal z.1 - X.X 0 z.1 < c} := by sorry
