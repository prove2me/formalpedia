-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys109_finite_atomless_mark_neighbourhood_mass_tends_zero
-- name    : AvramDividend.Classical.avram_bvb_phys109_finite_atomless_mark_neighbourhood_mass_tends_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:33:50.663201+00:00
-- url     : https://prove2.me/theorems/e6b3ee00-5c7a-4892-a530-07faa80f8da7
-- title:
--   Finite atomless jump-mark neighbourhoods have vanishing mass
-- statement:
--   For a finite real-valued jump-mark measure with zero atom at a fixed threshold, the mass of closed symmetric intervals shrinking to that threshold tends to zero. This is an important domination step in the physical-grid compensator quadrature.
-- source:
--   Official Mathlib theorem tendsto_measure_Icc_nhdsWithin_right', applied to finite jump-mark measures

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_phys109_finite_atomless_mark_neighbourhood_mass_tends_zero (μ : Measure ℝ) (hfinite : μ Set.univ < ⊤) (a : ℝ) (hatom : μ ({a} : Set ℝ) = 0) : Tendsto (fun δ : ℝ => μ (Icc (a - δ) (a + δ))) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by sorry
