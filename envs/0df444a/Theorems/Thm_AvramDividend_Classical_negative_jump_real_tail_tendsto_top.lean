-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_real_tail_tendsto_top
-- name    : AvramDividend.Classical.negative_jump_real_tail_tendsto_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:11:27.350702+00:00
-- url     : https://prove2.me/theorems/2cde304a-3060-4be7-ac2a-b48c96e45367
-- title:
--   Infinite Lévy negative activity makes the real truncated tail diverge continuously at zero
-- statement:
--   Infinite total negative Lévy intensity and the finite Lévy quadratic moment imply that the ordinary real intensity of jumps below -x diverges as the strictly positive cutoff x approaches zero. This strengthens the proved sequence-based finite-band Poisson-rate divergence to a full positive-right-neighbourhood statement using monotonicity of tail measures. It is the deterministic divergence needed to combine an eventual derivative-versus-tail lower bound with the canonical extended right derivative at zero.
-- source:
--   Proved negative_jump_real_poisson_rates_tendsto_top (25e87aea-e2cc-4603-a440-f9c9d277ee8d) and negative_jump_truncation_measure_finite (16a2d301-ca20-4837-969a-892ae00966c0).

import Theorems.Thm_AvramDividend_Classical_negative_jump_real_poisson_rates_tendsto_top
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Defs

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.negative_jump_real_tail_tendsto_top
    (ν : Measure ℝ)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν < ⊤)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤) :
    Tendsto (fun x : ℝ => (ν (Iio (-x))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry
