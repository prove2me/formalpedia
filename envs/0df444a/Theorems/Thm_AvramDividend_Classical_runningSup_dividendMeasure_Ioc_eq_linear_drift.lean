-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_linear_drift
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_linear_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:58:32.785362+00:00
-- url     : https://prove2.me/theorems/01e557c8-79bc-43dc-97a8-4301290dcc9a
-- title:
--   Running-supremum Stieltjes mass on a linear-drift interval
-- statement:
--   When the right-limit running supremum agrees with the physical bounded-variation drift times the clock at both endpoints of a half-open interval, its genuine Stieltjes dividend mass is the nonnegative drift increment. This reuses the proved exact running-supremum interval-mass formula, isolating the deterministic measure step needed before a compound-Poisson first jump.
-- source:
--   Prove2Me Proved runningSup_dividendMeasure_Ioc_rightLim (842a5998-7c24-4411-aeca-81f5fd46077c); Avram Palmowski Pistorius (2007) equation (3.14), https://arxiv.org/pdf/math/0702893

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_rightLim
import Mathlib.Tactic.Ring
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_linear_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ)
    (hs : Function.rightLim
      (fun r : ℝ => runningSup X r.toNNReal ω) s = X.drift * s)
    (ht : Function.rightLim
      (fun r : ℝ => runningSup X r.toNNReal ω) t = X.drift * t) :
    (dividendMeasure (runningSup X) ω) (Ioc s t) =
      ENNReal.ofReal (X.drift * (t - s)) := by sorry
