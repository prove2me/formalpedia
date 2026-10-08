-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrableOn_Iio_zero_of_isBigO_sq_of_bound
-- name    : AvramDividend.Classical.integrableOn_Iio_zero_of_isBigO_sq_of_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T11:50:30.630414+00:00
-- url     : https://prove2.me/theorems/b66078f4-7c86-46dd-a841-a7713423d1b5
-- title:
--   Quadratic-near-zero and bounded-away estimates imply Lévy-jump integrability
-- statement:
--   Pure measure/asymptotic helper for Lévy generators. Suppose min(1,y^2) is ν-integrable, F is a.e. strongly measurable, F(y)=O(y^2) as y→0, and F is uniformly bounded on the negative half-line. Then F is integrable over (-∞,0). Choose a small radius d≤1 on which the O(y^2) estimate holds. On |y|<d, F is dominated by C min(1,y^2). On y<0 with |y|≥d, min(1,y^2) is bounded below by d^2, so the uniform bound is again a constant multiple of min(1,y^2).
-- source:
--   Generic domination lemma tailored to the Lévy-measure integrability condition ∫ min(1,y²) ν(dy)<∞.

import Mathlib

open MeasureTheory Set Filter Asymptotics
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.integrableOn_Iio_zero_of_isBigO_sq_of_bound
    (ν : Measure ℝ)
    (hν : Integrable (fun y : ℝ => min 1 (y ^ 2)) ν)
    (F : ℝ → ℝ) (hF : AEStronglyMeasurable F ν)
    (hsmall : F =O[𝓝 0] (fun y : ℝ => y ^ 2))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ y : ℝ, y < 0 → ‖F y‖ ≤ B) :
    IntegrableOn F (Iio 0) ν := by sorry
