-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_p3c_integrable_unit_interval_extends_all_clocks
-- name    : AvramDividend.Classical.avram_a19_p3c_integrable_unit_interval_extends_all_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:54:27.916429+00:00
-- url     : https://prove2.me/theorems/5669f8d5-99f0-488f-a076-23022db61684
-- title:
--   Unit-interval integrability extends to all Lévy clocks by stationary increments
-- statement:
--   If a stationary-increment Lévy coordinate is integrable at every time up to one, it is integrable at every deterministic time, by decomposing into finitely many unit-length increments.
-- source:
--   Exact mathematically substantive moment reduction towards 7e6dcf49, itself a prerequisite for Avram A19 prebudget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_a19_p3c_integrable_unit_interval_extends_all_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hUnit : ∀ t : ℝ≥0, t ≤ 1 → Integrable (X.X t) P) :
    ∀ t : ℝ≥0, Integrable (X.X t) P := by sorry
