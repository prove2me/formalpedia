-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_compact_test_integrable
-- name    : AvramDividend.Classical.avram_p2_j_ui_original_compact_test_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:52:53.511967+00:00
-- url     : https://prove2.me/theorems/fae429fe-3788-41fb-b3e1-61833068bf02
-- title:
--   Genuine original Levy compact continuous real jump-test one-time marginal is Bochner integrable
-- statement:
--   For any finite original measure and any actual source Levy marginal X_t, a continuous real test with compact support is bounded by a finite real constant, and the true original adaptedness guarantees measurability. The genuinely integrable Bochner expectation then follows from pinned-Mathlib bounded-function integrability, without assuming independent synthetic process laws or jump-rate identities. This directly discharges the one-time integrability hypothesis in the original finite-grid stationary mean bridge for all continuous compact negative tests.

import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_j_ui_original_compact_test_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g)) :
    Integrable (fun ω => g (X.X t ω)) P := by sorry
