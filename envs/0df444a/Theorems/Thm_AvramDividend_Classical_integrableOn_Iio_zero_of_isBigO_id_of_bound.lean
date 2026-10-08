-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrableOn_Iio_zero_of_isBigO_id_of_bound
-- name    : AvramDividend.Classical.integrableOn_Iio_zero_of_isBigO_id_of_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T15:03:57.218292+00:00
-- url     : https://prove2.me/theorems/f62013cc-8202-4ca1-b410-a89182641ca4
-- title:
--   Linear-near-zero and bounded-away estimates imply bounded-variation Levy-jump integrability
-- statement:
--   Pure measure/asymptotic helper for bounded-variation Levy generators. Assume min(1,y^2) is ν-integrable, |y| is integrable over (-1,0), F is a.e. strongly measurable, F(y)=O(y) as y→0, and F is uniformly bounded on the negative half-line. Then F is integrable on (-∞,0). Near zero the O(y) estimate is dominated by the integrable |y| first-moment kernel. Away from zero the uniform bound is dominated by a constant multiple of min(1,y^2), exactly as in the quadratic helper.
-- source:
--   Generic domination lemma tailored to the bounded-variation Levy conditions.

import Mathlib

open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.integrableOn_Iio_zero_of_isBigO_id_of_bound
    (ν : Measure ℝ)
    (hνsq : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν)
    (hνabs : IntegrableOn (fun y : ℝ => |y|) (Ioo (-1) 0) ν)
    (F : ℝ → ℝ) (hF : AEStronglyMeasurable F ν)
    (hsmall : F =O[𝓝 0] (fun y : ℝ => y))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y : ℝ, y < 0 → ‖F y‖ ≤ B) :
    IntegrableOn F (Iio 0) ν := by sorry
