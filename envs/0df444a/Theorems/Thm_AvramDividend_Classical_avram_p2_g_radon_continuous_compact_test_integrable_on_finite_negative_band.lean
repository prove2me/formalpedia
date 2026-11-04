-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_g_radon_continuous_compact_test_integrable_on_finite_negative_band
-- name    : AvramDividend.Classical.avram_p2_g_radon_continuous_compact_test_integrable_on_finite_negative_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:05:00.06587+00:00
-- url     : https://prove2.me/theorems/5c4ff8c9-52bb-47fc-bace-1ecbf655e77f
-- title:
--   Compact continuous negative-band tests are integrable for any measure finite on the supporting band
-- statement:
--   If a real-valued continuous compactly supported test vanishes off a negative band whose measure is finite, its global integral against that measure is absolutely integrable, regardless of whether the underlying measure has infinite mass near zero. This establishes the exact deterministic integrability property required for arbitrary original Lévy measures restricted to separated negative marks, without assuming any Lévy jump intensity identity.
-- source:
--   Mathlib.MeasureTheory.Integral.IntegrableOn: IntegrableOn.of_bound and integrableOn_iff_integrable_of_support_subset; Mathlib.Topology.Algebra.Support: HasCompactSupport.exists_bound_of_continuous.

import Mathlib
open MeasureTheory Set Topology
noncomputable section

theorem AvramDividend.Classical.avram_p2_g_radon_continuous_compact_test_integrable_on_finite_negative_band
    (μ : Measure ℝ) (g : ℝ → ℝ)
    (hcont : Continuous g) (hcompact : HasCompactSupport g)
    {ε : ℝ} (hμ : μ (Iic (-ε)) < ⊤)
    (hsupp : Function.support g ⊆ Iic (-ε)) :
    Integrable g μ := by sorry
