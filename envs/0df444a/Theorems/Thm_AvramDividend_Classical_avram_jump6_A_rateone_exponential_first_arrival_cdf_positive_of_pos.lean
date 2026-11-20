-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_rateone_exponential_first_arrival_cdf_positive_of_pos
-- name    : AvramDividend.Classical.avram_jump6_A_rateone_exponential_first_arrival_cdf_positive_of_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:25:57.628252+00:00
-- url     : https://prove2.me/theorems/0f4eabb8-829a-42bc-830b-17f398bb7738
-- title:
--   Exponential rate-one first-arrival cumulative probability positive at every positive horizon
-- statement:
--   For every positive horizon t, a rate-one exponential first-arrival time occurs by t with positive probability. Prove directly from the exact Mathlib exponential CDF identity and monotonicity of the exponential. In particular, this provides a time 1/500 source aligned with the existing positive Brownian tube duration, improving the preceding 1/10-specific lemma.

import Mathlib
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_rateone_exponential_first_arrival_cdf_positive_of_pos
    (t : ℝ) (ht : 0 < t) :
    0 < cdf (expMeasure (1 : ℝ)) t := by sorry
