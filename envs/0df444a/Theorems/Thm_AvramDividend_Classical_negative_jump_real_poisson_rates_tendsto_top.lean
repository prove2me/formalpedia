-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_real_poisson_rates_tendsto_top
-- name    : AvramDividend.Classical.negative_jump_real_poisson_rates_tendsto_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:44:02.090396+00:00
-- url     : https://prove2.me/theorems/25e87aea-e2cc-4603-a440-f9c9d277ee8d
-- title:
--   Real Poisson intensities for finite negative bands diverge under infinite activity
-- statement:
--   An infinite-activity Lévy measure has arbitrarily large intensities for negative jump-size bands approaching zero. The Lévy integrability condition makes each band mass finite, allowing the extended-real mass to be converted to a real Poisson parameter. Multiplication by any strictly positive time horizon preserves divergence to infinity.
-- source:
--   Avram, Palmowski and Pistorius (2007), zero-barrier infinite-activity branch, https://arxiv.org/pdf/math/0702893; Lévy measure truncation finiteness and continuity from below.

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Order.Filter.AtTopBot.Field

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

/-- Finite jump-band rates at every positive time horizon diverge under infinite activity. -/
theorem negative_jump_real_poisson_rates_tendsto_top
    (ν : Measure ℝ)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤)
    (t : ℝ) (ht : 0 < t) :
    Tendsto
      (fun n : ℕ => t * (ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)
      atTop atTop := by sorry

end AvramDividend.Classical
