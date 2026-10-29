-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_fixed_infimum_zero_atoms_of_exp_clock_ws01f
-- name    : AvramDividend.Classical.levy_fixed_infimum_zero_atoms_of_exp_clock_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:47:38.908794+00:00
-- url     : https://prove2.me/theorems/48f3a175-37a6-4ba1-9a89-f96ccec3a0e7
-- title:
--   Original Lévy exponential-clock running-infimum zero atom nullity implies every fixed-horizon zero atom vanishes
-- statement:
--   Under an actual positive-rate independent exponential clock, if the original-law zero atom of the negative running infimum vanishes, then the zero atom of the same running infimum vanishes for every deterministic positive horizon. Use original pathwise survival equivalence, positive exponential-clock mass of every positive early interval and product-measure monotonicity.
-- source:
--   Proved levy_exp_clock_survival_null_fixed_horizon_ws01f, exp_clock_Iic_strictly_positive_ws01f, chat04_reflected_infimum_Iic_iff_survival, chat04_negative_running_infimum_nonneg.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_negative_running_infimum_nonneg
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_levy_exp_clock_survival_null_fixed_horizon_ws01f
import Theorems.Thm_AvramDividend_Classical_exp_clock_Iic_strictly_positive_ws01f

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_fixed_infimum_zero_atoms_of_exp_clock_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (hClockAtom : (P.prod (expMeasure p))
      {z : Ω × ℝ |
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1} = 0} = 0) :
    ∀ t : ℝ≥0, 0 < t →
      P {ω : Ω |
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ t ∧ y = X.X s ω} = 0} = 0 := by sorry
