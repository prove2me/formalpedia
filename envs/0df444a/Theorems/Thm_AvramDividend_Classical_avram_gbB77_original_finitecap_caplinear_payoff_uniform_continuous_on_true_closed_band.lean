-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB77_original_finitecap_caplinear_payoff_uniform_continuous_on_true_closed_band
-- name    : AvramDividend.Classical.avram_gbB77_original_finitecap_caplinear_payoff_uniform_continuous_on_true_closed_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:41:40.449542+00:00
-- url     : https://prove2.me/theorems/2b5fcde3-f1d8-4250-8b44-bd1e0eb96c25
-- title:
--   Original interior caplinear finite-cap payoff uniformly continuous on any true compact nonnegative reserve band despite kink
-- statement:
--   Under the original candidate assumption w continuous on [0,∞), its interior caplinear continuation V_b is uniformly continuous on every finite compact nonnegative reserve band [0,K], including the derivative kink b and the lower contact level zero. It follows from V_b(y)=w(min(y,b))+(y-b)^+ and compactness, requiring no C2 at b. This supplies source-faithful spatial stopping-crossing value modulus for proving B54 positive L1.
-- source:
--   B76 exact caplinear min-plus-positive-part representation; min, subtraction and max are continuous; w∘min is continuous on nonnegative reserve states since b≥0; Heine-Cantor on compact Icc(0,K) establishes uniform continuity.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB76_original_interior_caplinear_value_exact_minplus_positive_part
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB77_original_finitecap_caplinear_payoff_uniform_continuous_on_true_closed_band
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (b K : ℝ) (hb : 0 ≤ b) :
    let V : ℝ → ℝ := fun y =>
      if y ≤ b then w y else w b + (y - b)
    UniformContinuousOn V (Icc 0 K) := by sorry
