-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrableOn_Icc_of_continuousOn_finite_measure
-- name    : AvramDividend.Classical.integrableOn_Icc_of_continuousOn_finite_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:02:35.649405+00:00
-- url     : https://prove2.me/theorems/9d594cd0-4c25-4a9d-9952-5404338bb2f9
-- title:
--   A continuous real function on a compact interval is integrable for every finite measure
-- statement:
--   For any finite real measure μ, a real function continuous on a nonempty compact interval [l,u] is integrable on that interval. Compactness attains the maximum of the norm of f; this constant bound and a.e.-strong measurability yield Bochner integrability on the finite-measure restriction. Provides compact occupation-measure integrability of the continuous Lévy generator residual.
-- source:
--   Pinned Mathlib compact maximum principle, ContinuousOn.aestronglyMeasurable_of_isCompact and IntegrableOn.of_bound.

import Mathlib

open MeasureTheory Set

namespace AvramDividend.Classical

theorem integrableOn_Icc_of_continuousOn_finite_measure
    (f : ℝ → ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (l u : ℝ) (hlu : l ≤ u)
    (hf : ContinuousOn f (Icc l u)) :
    IntegrableOn f (Icc l u) μ := by sorry

end AvramDividend.Classical
