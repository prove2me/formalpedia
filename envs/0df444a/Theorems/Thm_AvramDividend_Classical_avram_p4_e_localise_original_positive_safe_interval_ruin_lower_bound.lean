-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_positive_safe_interval_ruin_lower_bound
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_positive_safe_interval_ruin_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:38:17.732234+00:00
-- url     : https://prove2.me/theorems/2eacf648-9646-411e-b1e4-9a8f0db84b88
-- title:
--   Original controlled reserve safe interval forces the true ruin clock past that interval
-- statement:
--   For the exact source ruinTime as the infimum of strict-negative reserve times, a pointwise nonnegative reserve on [0, ε) forces ruinTime at least ε. This is a genuine original-process deterministic bridge usable with a separate right-continuity proof establishing a safe initial interval at cap-start. It assumes safety explicitly and does not claim such safety automatically.
-- source:
--   Source ruinTime and riskProcess definitions from AvramDividend.Classical.DividendStrategy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A genuinely nonnegative initial source reserve interval bounds the strict-negative ruin time below. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_positive_safe_interval_ruin_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (ε : ℝ≥0)
    (hSafe : ∀ t : ℝ≥0, t < ε → 0 ≤ riskProcess X x D t ω) :
    (ε : ℝ≥0∞) ≤ ruinTime X x D ω := by sorry
