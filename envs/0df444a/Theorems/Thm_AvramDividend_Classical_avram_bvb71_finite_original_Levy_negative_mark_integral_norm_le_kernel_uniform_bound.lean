-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb71_finite_original_Levy_negative_mark_integral_norm_le_kernel_uniform_bound
-- name    : AvramDividend.Classical.avram_bvb71_finite_original_Levy_negative_mark_integral_norm_le_kernel_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:51:54.164993+00:00
-- url     : https://prove2.me/theorems/579f4d6f-56a9-4d3e-9ae0-559427bd8c9f
-- title:
--   Finite original negative Lévy measure uniformly bounded marked kernel integral has deterministic K times intensity norm bound
-- statement:
--   For the original finite negative-jump Lévy intensity restricted to any measurable negative Borel mark set S of finite mass, a real kernel f uniformly bounded in absolute value by K≥0 has Bochner integral norm at most K times the finite real intensity ν(S). This is the single-fibre bound in source BVB68, to be integrated over the true time interval [0,T].
-- source:
--   Proved a21_borel_mark_intensity_bound_20261113 pure source proof and MeasureTheory.norm_integral_le_of_norm_le_const, original BVB68 compensator.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb71_finite_original_Levy_negative_mark_integral_norm_le_kernel_uniform_bound
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hMass : ν S < ⊤) (f : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hBound : ∀ z ∈ S, |f z| ≤ K) :
    ‖∫ z in S, f z ∂ν‖ ≤ K * (ν S).toReal := by sorry
