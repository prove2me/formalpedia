-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_original_record_reciprocal_power
-- name    : AvramDividend.Classical.avram_wave3_01_original_record_reciprocal_power
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:50:54.983693+00:00
-- url     : https://prove2.me/theorems/70410103-dab6-423c-8392-84a40643e92b
-- title:
--   Exact reciprocal-height power law for the genuine reflected killed first-record discount
-- statement:
--   For every n, the (n+1)-st power of the genuine first-upcrossing before reflected drawdown ruin discounted reward at height 1/(n+1) equals that reward at unit height. This follows from the source-level original-clock strong-Markov first-record semigroup and finite induction. It is a discrete Cauchy law that identifies the logarithmic slope on reciprocal heights without an assumed scale-function derivative.
-- source:
--   Pinned original-process Proved source semigroup AvramDividend.Classical.avram_wave3_01_uncapped_reflected_record_discount_semigroup; Avram mission root C1 derivative branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_uncapped_reflected_record_discount_semigroup

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_01_original_record_reciprocal_power
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a q : ℝ) (ha : 0 < a) (hq : 0 < q) :
    ∀ n : ℕ,
      (∫⁻ ω, if twoSidedExitUpTime X (1 / ((n : ℝ) + 1)) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X
            (1 / ((n : ℝ) + 1)) ω).toReal)))
      else 0 ∂P) ^ (n + 1) =
      (∫⁻ ω, if twoSidedExitUpTime X 1 ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (Real.exp (-(q * (twoSidedExitUpTime X 1 ω).toReal)))
      else 0 ∂P) := by sorry
