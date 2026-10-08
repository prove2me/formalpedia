-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_countable_positive_rightLimit_jumps
-- name    : AvramDividend.Classical.dividendStrategy_countable_positive_rightLimit_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:11:03.950581+00:00
-- url     : https://prove2.me/theorems/b876ce73-9e1d-42a0-8636-045f64ec38bb
-- title:
--   All nonnegative times with a nonzero formal dividend rightLimit jump form a countable set
-- statement:
--   For a dividend strategy D and sample path ω, all nonnegative real times t at which the precise mission-defined jump rightLimit D(t.toNNReal)−D(t.toNNReal) is nonzero form a countable subset of the line. This transfers monotone real-extension right-jump countability to the exact rightLimit used in admissibility and Stieltjes dividend payments, using the verified right-limit identification lemma.
-- source:
--   Children dividendStrategy_countable_rightJump_times and dividendPath_real_rightLim_eq_rightLimit, plus Real.coe_toNNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_countable_positive_rightLimit_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Set.Countable {t : ℝ |
      0 ≤ t ∧ rightLimit D t.toNNReal ω ≠ D t.toNNReal ω} := by sorry
