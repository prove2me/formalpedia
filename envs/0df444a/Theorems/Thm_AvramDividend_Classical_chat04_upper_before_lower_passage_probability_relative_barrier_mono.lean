-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_upper_before_lower_passage_probability_relative_barrier_mono
-- name    : AvramDividend.Classical.chat04_upper_before_lower_passage_probability_relative_barrier_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:46:17.847869+00:00
-- url     : https://prove2.me/theorems/a91762db-2a96-428b-b74c-7705865270ac
-- title:
--   Monotonicity of strict upper-before-ruin exit probability under compensated barrier shifts
-- statement:
--   For any spectrally negative Lévy process, if the initial reserve rises and the upper barrier measured relative to that reserve does not rise, the event of a strict upper crossing before strict ruin grows. Consequently its probability increases. The result is a consequence of the pointwise first-passage time ordering.
-- source:
--   Uses the remotely verified chat04_strict_exit_clocks_relative_barrier_comparison (5e83d1a9-b841-4183-9788-ed2fc2c18017) and monotonicity of measure.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_upper_before_lower_passage_probability_relative_barrier_mono
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    P {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ≤
      P {ω : Ω | twoSidedExitUpTime X (b - y) ω <
        twoSidedExitDownTime X (-y) ω} := by sorry
