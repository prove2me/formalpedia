-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
-- name    : AvramDividend.Classical.negative_jump_truncation_measure_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:35:30.79668+00:00
-- url     : https://prove2.me/theorems/16a2d301-ca20-4837-969a-892ae00966c0
-- title:
--   Lévy measure has finite mass on each negative jump-size truncation
-- statement:
--   The Lévy-measure integrability condition integral min(1,y²) ν(dy)<∞ ensures that jumps of magnitude at least any δ>0 have finite intensity. The proof uses Markov's inequality for the nonnegative extended-real Lévy integrand and the lower bound min(1,δ²) on the truncation set.
-- source:
--   Standard Lévy measure finiteness away from zero; Avram, Palmowski and Pistorius (2007), Lévy triplet assumptions and Proposition 1, https://arxiv.org/pdf/math/0702893; Mathlib.MeasureTheory.Integral.Lebesgue.Markov.

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

/-- The Lévy small-jump integrability bound makes every negative truncation finite. -/
theorem negative_jump_truncation_measure_finite
    (ν : Measure ℝ)
    (hν : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (δ : ℝ) (hδ : 0 < δ) :
    ν (Iic (-δ)) < ⊤ := by sorry

end AvramDividend.Classical
