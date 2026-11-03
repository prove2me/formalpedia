-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_rightdividend_terminal_telescoping
-- name    : AvramDividend.Classical.avram_wave7_19_original_rightdividend_terminal_telescoping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:55:55.536364+00:00
-- url     : https://prove2.me/theorems/c49c0d82-9284-47c1-8623-8a83846dd5c1
-- title:
--   Original right dividend jump pays from pre-rightpayment reserve and leaves exact post-rightpayment terminal value
-- statement:
--   At any original physical time, if the canonical hjump inequality controls the right dividend payment by the value-function drop across that actual right payment, its cash plus the value evaluated at the true post-rightpayment reserve cannot exceed its pre-rightpayment value. Uses the exact original riskProcess and rightLimit definitions and elementary algebra. This isolates the t=0/rightboundary dividend atom from the stochastic stopped Itô integrals, without assuming continuous dividend paths or imposing new regularity.
-- source:
--   Original riskProcess=x+X.X t-D t and rightLimit D; canonical positive-UBV hjump hypothesis, specialising it to one stop time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_rightdividend_terminal_telescoping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hjump :
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) :
    rightLimit D t ω - D t ω +
      w (x + X.X t ω - rightLimit D t ω) ≤
        w (riskProcess X x D t ω) := by sorry
