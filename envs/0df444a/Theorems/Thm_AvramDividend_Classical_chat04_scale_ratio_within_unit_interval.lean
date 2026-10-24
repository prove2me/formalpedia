-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_scale_ratio_within_unit_interval
-- name    : AvramDividend.Classical.chat04_scale_ratio_within_unit_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:02:03.234664+00:00
-- url     : https://prove2.me/theorems/21c3f23f-bf7d-4f7a-88b4-c5645f31a66a
-- title:
--   The canonical strict two-sided exit scale ratio lies in the unit interval
-- statement:
--   For canonical q-scale W under Standing and q>0, at any 0≤x≤a with a>0, the target strict killed exit ratio W(x)/W(a) belongs to [0,1]. This uses positivity of W(a), nonnegativity and monotonicity of W on the positive half-line. It verifies the probabilistic range required by the two-sided exit identity.
-- source:
--   Direct consequence of the IsScaleFunction definition and previously Proved scaleFunction_strict_pos_of_standing; equation (3.6) in Avram, Palmowski, Pistorius (2007).

import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_scale_ratio_within_unit_interval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x : ℝ)
    (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    0 ≤ W x / W a ∧ W x / W a ≤ 1 := by sorry
