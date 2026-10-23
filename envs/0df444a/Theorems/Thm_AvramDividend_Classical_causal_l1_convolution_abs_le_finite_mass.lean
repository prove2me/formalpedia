-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_abs_le_finite_mass
-- name    : AvramDividend.Classical.causal_l1_convolution_abs_le_finite_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T23:21:16.689547+00:00
-- url     : https://prove2.me/theorems/db15bf0a-57a2-4d17-bbf9-2f0f6e51a855
-- title:
--   Finite-horizon L1 convolution controlled by input supremum and truncated kernel mass
-- statement:
--   For K∈L1(0,∞) and a positive-time continuous locally bounded V, the absolute causal convolution at 0<x≤R is bounded by sup_{0<s≤R}|V(s)| times the truncated kernel mass ∫₀ˣ|K(t)|dt. Apply the existing weighted causal product estimate with weight zero, the Bochner integral norm bound and causal time reversal. This is a quantitative small-time estimate needed to show the Volterra operator preserves continuity at zero.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_locally_bounded_input_integrable
import Theorems.Thm_AvramDividend_Classical_causal_weighted_sup_bddAbove_of_locally_bounded
import Theorems.Thm_AvramDividend_Classical_causal_weighted_kernel_product_le_sup_mass
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_convolution_abs_le_finite_mass
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C)
    (R x : ℝ) (hR : 0 < R) (hx : x ∈ Ioc (0 : ℝ) R) :
    |∫ s in Ioc (0 : ℝ) x, K (x - s) * V s ∂volume| ≤
      sSup ((fun s : ℝ => |V s|) '' Ioc (0 : ℝ) R) *
        (∫ s in Ioc (0 : ℝ) x, |K s| ∂volume) := by sorry
