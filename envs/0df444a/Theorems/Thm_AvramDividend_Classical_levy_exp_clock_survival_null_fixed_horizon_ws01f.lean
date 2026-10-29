-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exp_clock_survival_null_fixed_horizon_ws01f
-- name    : AvramDividend.Classical.levy_exp_clock_survival_null_fixed_horizon_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:32:18.905985+00:00
-- url     : https://prove2.me/theorems/bab34380-b847-4058-9e2a-767b49d34c7d
-- title:
--   A full-probability genuine exponential-clock downward crossing eliminates fixed-horizon survival mass
-- statement:
--   For the actual source Lévy paths, suppose the product law P×Exp(p) assigns zero mass to paths staying nonnegative until the sampled exponential clock. At a deterministic time T for which the exponential clock has strictly positive mass of occurring by T, the original law P assigns zero mass to paths staying nonnegative throughout [0,T]. This is the genuine product-measure rectangle and clock-monotonicity bridge needed to transport a Wiener–Hopf zero-atom conclusion to deterministic horizons.
-- source:
--   Pinned Mathlib Measure.prod_prod and Real.toNNReal_mono, true expMeasure probability for p>0, and monotonicity of the pathwise survival predicate. No unproved source fluctuation identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exp_clock_survival_null_fixed_horizon_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p T : ℝ) (hp : 0 < p)
    (hClockPos : 0 < (expMeasure p) (Iic T))
    (hClockNull :
      (P.prod (expMeasure p))
        {z : Ω × ℝ | ∀ s : ℝ≥0,
          s ≤ z.2.toNNReal → 0 ≤ X.X s z.1} = 0) :
    P {ω : Ω | ∀ s : ℝ≥0,
      s ≤ T.toNNReal → 0 ≤ X.X s ω} = 0 := by sorry
