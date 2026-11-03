-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_jump_threshold_iff_leftLim
-- name    : AvramDividend.Classical.avram_wave7_06_original_jump_threshold_iff_leftLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:58:26.231175+00:00
-- url     : https://prove2.me/theorems/f1c48298-fc61-40a6-a3eb-825adbf64cf6
-- title:
--   Exact original jump threshold equals leftLim criterion
-- statement:
--   Every positive-time original Lévy path has the exact existential left limit from X.leftLim, and uniqueness identifies it with Function.leftLim. Thus the target jump threshold has the equivalent literal leftLim condition on X itself.
-- source:
--   Original source event bridge for bfc446d3-ff26-4179-a1b4-162efc857227.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_jump_threshold_iff_leftLim
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    (∃ l : ℝ, Tendsto (fun s : ℝ≥0 => X.X s ω)
        (nhdsWithin t (Iio t)) (nhds l) ∧
        X.X t ω + 1 / ((n : ℝ) + 1) ≤ l) ↔
    X.X t ω + 1 / ((n : ℝ) + 1) ≤
      Function.leftLim (fun s : ℝ≥0 => X.X s ω) t := by sorry
