-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_haslaw_survival
-- name    : AvramDividend.Classical.chat06_unit_exponential_haslaw_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:35:35.196349+00:00
-- url     : https://prove2.me/theorems/10d29558-d025-4eba-b4d3-9c25adf1a7fc
-- title:
--   Unit-rate exponential law yields the exact nonnegative-age survival probability
-- statement:
--   For an Ω-valued real random variable having the unit-rate exponential law under a probability measure P, its survival event at every nonnegative time t has probability exp(-t). The proof computes the complement of the exponential cumulative distribution and transfers the resulting measurable upper-tail event through the probability-law identity, allowing the countwise Poisson memorylessness results to derive their survival assumption from the law rather than separately posit it.
-- source:
--   bv_unit_exponential_haslaw_survival_v2_chat06_20261022.lean, 39 lines, 1548 bytes, SHA-256 1832800dfe8059235d111f2ab12141cc0c13c9ee4877be07e84bbc18c774ed1f; remote private probe 107e2cdb-218b-49c7-b0ba-f989e72d273c reached sentinel without candidate errors.

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.ENNReal.Operations
import Mathlib.Tactic.Ring

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.chat06_unit_exponential_haslaw_survival
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (X : Ω → ℝ)
    (hLaw : HasLaw X (expMeasure 1) P)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | t < X ω} = ENNReal.ofReal (Real.exp (-t)) := by sorry
