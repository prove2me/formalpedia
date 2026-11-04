-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_large_mark_raw_indicator_identity
-- name    : AvramDividend.Classical.avram_p4_c_generator_large_mark_raw_indicator_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:25:37.108192+00:00
-- url     : https://prove2.me/theorems/4c6beffc-efa2-4dd4-bb61-b1e7cf2e2e87
-- title:
--   Original large negative mark raw jump equals source compensated generator kernel plus exact finite-annulus indicator drift
-- statement:
--   For every large negative mark z<-epsilon with 0<epsilon<1, the raw payoff jump is precisely the source generatorIntegrand plus w'(y)z on -1<z<-epsilon, expressed by the measured indicator. The case z≤-1, including z=-1, has no derivative compensation, because the original source truncation (-1,1) is strict. The case -epsilon is excluded from large marks. This pointwise identity can be lifted to predictable source jump counting measures once P2 supplies its compensator; no stochastic equality is postulated here.
-- source:
--   Exact original SpectrallyNegativeLevy.generatorIntegrand strict unit indicator

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_large_mark_raw_indicator_identity
    (w : ℝ → ℝ) (y z ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hz : z ∈ Iio (-ε)) :
    w (y + z) - w y =
      SpectrallyNegativeLevy.generatorIntegrand w y z +
      deriv w y * (Ioo (-1 : ℝ) (-ε)).indicator (fun t : ℝ => t) z := by sorry
