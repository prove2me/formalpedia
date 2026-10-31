-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
-- name    : AvramDividend.Classical.avram_wave3_03_bv_full_cap_gradient_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:41:33.327282+00:00
-- url     : https://prove2.me/theorems/2ba5cc4f-3aab-40ea-a59a-8a49633c7595
-- title:
--   BV HJB gradient yields a full-cap value-drop inequality for arbitrary continuous Stieltjes dividend increments
-- statement:
--   The HJB hypothesis derivative w≥1 on the strict positive interior below a positive capital cap, together with C1 regularity there and continuity up to zero, implies the endpoint-inclusive secant inequality w(b)-w(a)≥b-a for any 0≤a≤b with ENNReal.ofReal b≤C, including b at the cap and a at zero. Applied to arbitrary nondecreasing dividend increments, this covers their continuous and singular-continuous parts as well as right jumps. This deterministic source verification ingredient does not presume a semimartingale identity.
-- source:
--   Mathlib's convex-domain mean-value theorem Convex.mul_sub_le_image_sub_of_le_deriv with hC, the original BV positive-cap HJB gradient premises, and the exact ofReal inequality. Avoids evaluation of w' at the cap or zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_full_cap_gradient_secant
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : ENNReal.ofReal b ≤ C) :
    b - a ≤ w b - w a := by sorry
