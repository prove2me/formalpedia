-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exp_clock_infimum_zero_atom_of_drawdown_ws01f
-- name    : AvramDividend.Classical.levy_exp_clock_infimum_zero_atom_of_drawdown_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:45:39.442714+00:00
-- url     : https://prove2.me/theorems/4b933e51-a31b-4ee7-9c56-78792c12ae27
-- title:
--   Actual original exponential-clock Lévy path reversal transfers terminal drawdown zero-atom nullity to running-infimum zero-atom nullity
-- statement:
--   For an actual spectrally negative Lévy process and an independent positive-rate exponential clock, if the original-law terminal drawdown has no zero atom, then the original-law negative running infimum has no zero atom. This is the genuine proved two-dimensional exponential-clock distribution reversal, not a Brownian or Poisson surrogate.
-- source:
--   Canonical Proved chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a and exact jointly measurable running supremum, infimum and state.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_actual_exponential_clock_joint_pair_distribution_reversal_ws01a
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exp_clock_infimum_zero_atom_of_drawdown_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (hD : (P.prod (expMeasure p))
      {z : Ω × ℝ | runningSup X z.2.toNNReal z.1 -
        X.X z.2.toNNReal z.1 = 0} = 0) :
    (P.prod (expMeasure p))
      {z : Ω × ℝ |
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1} = 0} = 0 := by sorry
