-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_global_secant
-- name    : AvramDividend.Classical.avram_p3_bv_finite_cap_linear_global_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T14:16:19.881737+00:00
-- url     : https://prove2.me/theorems/849da3fc-079a-43c1-86c9-f1144c420b48
-- title:
--   Original BV slope-one cap-linear continuation obeys every nonnegative dividend secant
-- statement:
--   For the canonical BV HJB candidate continuous on nonnegative reserves, C1 on the strict positive finite-cap interior and with interior derivative at least one, define its slope-one linear extension V above the finite positive cap. Then the dividend-value secant inequality b-a ≤ V(b)-V(a) holds globally for all nonnegative a≤b. Covers wholly below-cap, crossing-cap and wholly above-cap payments without requiring any regularity of original w above C or a smooth-fit derivative at C. The cap-linear extension is precisely the tool required to treat original-source cap contact safely.
-- source:
--   Join Proved BV full-cap secant 2ba5cc4f-3aab-40ea-a59a-8a49633c7595, Proved finite-cap crossing secant 244e0215-074e-4541-9754-de6dbede140f, and exact linear algebra above the cap. C1 only on (0,C), as in Proposition 4(i) of Avram, Palmowski and Pistorius.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_crossing_secant

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_finite_cap_linear_global_secant
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    let V : ℝ → ℝ := fun z =>
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    ∀ (a b : ℝ), 0 ≤ a → a ≤ b → b - a ≤ V b - V a := by sorry
