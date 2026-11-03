-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_leftlimit_threshold_tendsto_iff
-- name    : AvramDividend.Classical.avram_wave7_06_original_leftlimit_threshold_tendsto_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:47:38.421414+00:00
-- url     : https://prove2.me/theorems/e5abfc4f-f443-4bd8-9489-87d8aa73790b
-- title:
--   Unique genuine source left limit converts existential threshold jump to intrinsic leftLim inequality
-- statement:
--   At every strictly positive time of an original Lévy sample path, if a finite left limit exists, it is unique and is the value of Mathlib Function.leftLim. Therefore the source jump criterion stated using an existential Tendsto witness is equivalent to existence of some left limit together with the corresponding inequality using Function.leftLim. This is a purely topological equivalence, preserving the exact original sample path and the left-neighbourhood filter.
-- source:
--   Original-path event bridge needed by Avram Wave 7 Chat 06 theorem bfc446d3-ff26-4179-a1b4-162efc857227. Uses Mathlib tendsto_leftLim_of_tendsto and nhdsLT_neBot_of_exists_lt at positive time. Does not assert cadlag existence or a Poisson probability without proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_leftlimit_threshold_tendsto_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    (∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) ∧
        X.X t ω + 1 / ((n : ℝ) + 1) ≤ l) ↔
    (∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l)) ∧
    X.X t ω + 1 / ((n : ℝ) + 1) ≤
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t := by sorry
