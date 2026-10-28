-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_weighted_positive_envelope_normalized_lt_one
-- name    : AvramDividend.Classical.causal_weighted_positive_envelope_normalized_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:21:16.610903+00:00
-- url     : https://prove2.me/theorems/ef300e60-94d2-4ecb-8c24-795b92c3d40b
-- title:
--   Normalised positive Gaussian kernel has weighted mass below one
-- statement:
--   For a strictly positive Gaussian coefficient a and positive exponential damping rate, the signed drift's positive envelope, scaled by 1/a, is integrable over positive time and has total mass strictly below one. This is exactly the geometric contraction bound for the nonnegative convolution-power dominating kernel.
-- source:
--   Consequence of the accepted causal_weighted_positive_envelope_mass_lt_a and positive scalar normalisation.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_causal_weighted_positive_envelope_mass_lt_a

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_weighted_positive_envelope_normalized_lt_one
    (K : ℝ → ℝ) (a β w : ℝ) (ha : 0 < a) (hw : 0 < w)
    (hKi : IntegrableOn (fun t : ℝ => Real.exp (-w * t) * K t)
      (Ioi (0 : ℝ)) volume)
    (hsmall : |β| / w +
      (∫ t in Ioi (0 : ℝ), |K t| * Real.exp (-w * t) ∂volume) < a) :
    IntegrableOn (fun t : ℝ =>
      a⁻¹ * Real.exp (-w * t) * (|β| + K t))
      (Ioi (0 : ℝ)) volume ∧
    (∫ t in Ioi (0 : ℝ),
      a⁻¹ * Real.exp (-w * t) * (|β| + K t) ∂volume) < 1 := by sorry
