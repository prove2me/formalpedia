-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_measurable_eventual_grid_limit
-- name    : AvramDividend.Classical.avram_p2_e_compensator_measurable_eventual_grid_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:02:40.861191+00:00
-- url     : https://prove2.me/theorems/be2be500-59a1-4dba-81fb-a1627a075eb6
-- title:
--   Eventually exact measurable original grid counts yield measurable chronological pair limit
-- statement:
--   When original source grid counts are each measurable and eventually equal a sample-path chronological pair count, the exact limit count is measurable as the pointwise liminf of the grid counts.
-- source:
--   Pinned Measurable.liminf and Filter.liminf_congr; complements accepted Fatou and source original grid measurability for final real integrability.

import Mathlib

open Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_measurable_eventual_grid_limit
    {Ω : Type*} [MeasurableSpace Ω]
    (G : ℕ → Ω → ℝ≥0∞) (K : Ω → ℝ≥0∞)
    (hMeas : ∀ n, Measurable (G n))
    (hEventual : ∀ ω, ∀ᶠ n in Filter.atTop, G n ω = K ω) :
    Measurable K := by sorry
