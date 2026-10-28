-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_levy_restricted_real_deficit_tendsto_atTop
-- name    : AvramDividend.Classical.negative_levy_restricted_real_deficit_tendsto_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:45:46.694524+00:00
-- url     : https://prove2.me/theorems/45a8aefe-d941-473a-87c8-3bf3ee38cec2
-- title:
--   Real exponential Lévy deficit over strictly negative jumps diverges under infinite activity
-- statement:
--   For any measure with infinite mass on strictly negative jumps, the integrable real exponential-deficit integral over that negative band diverges to +∞ with its Laplace argument. Restrict the measure to negative jumps; its nonnegative-support complement has zero mass and its negative mass is unchanged. Apply the already accepted real-integral divergence theorem to the restricted measure. The statement matches exactly the signed jump integral in the accepted bounded-variation Lévy exponent identity, with no global support condition.
-- source:
--   Monotone convergence and negative-jump Lévy–Khintchine formula, Kuznetsov Kyprianou Rivero and Avram Palmowski Pistorius (2007), https://arxiv.org/pdf/math/0702893

import Theorems.Thm_AvramDividend_Classical_negative_levy_real_exponential_deficit_tendsto_atTop
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

/-- Infinite negative jump activity forces divergence on the strictly negative band. -/
theorem negative_levy_restricted_real_deficit_tendsto_atTop
    (ν : Measure ℝ)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤)
    (hInt : ∀ n : ℕ, Integrable
      (fun y : ℝ => 1 - Real.exp ((n : ℝ) * y))
      (ν.restrict (Iio (0 : ℝ)))) :
    Tendsto
      (fun n : ℕ => ∫ y in Iio (0 : ℝ),
        (1 - Real.exp ((n : ℝ) * y)) ∂ν)
      atTop atTop := by sorry

end AvramDividend.Classical
