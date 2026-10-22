-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_jump_real_integrable
-- name    : AvramDividend.Classical.gaussian_levy_jump_real_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T08:35:28.100274+00:00
-- url     : https://prove2.me/theorems/f855dc5b-f625-4698-acfd-f72f76e81cfe
-- title:
--   Real integrability of canonical negative-jump Lévy exponent
-- statement:
--   For nonnegative θ and a Lévy jump-magnitude measure with finite truncated-square moment, the canonical real jump integrand exp(−θz)−1+θ z 1_{z≤1} is Bochner integrable on positive jump magnitudes. This is proved by converting the already controlled finite absolute ENNReal integral to integrability of the absolute value, then applying the norm-integrability equivalence. Combined with the proved Esscher compensator and drift integrability, it closes the four hypotheses needed to apply the real-valued Esscher-shift integral algebra.
-- source:
--   Requires proved gaussian_levy_jump_absolute_integrable; pinned lintegral_ofReal_ne_top_iff_integrable, Real.norm_eq_abs and integrable_norm_iff.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.gaussian_levy_jump_real_integrable
    (μ : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    IntegrableOn (fun z : ℝ =>
      Real.exp (-θ * z) - 1 +
        θ * (if z ≤ 1 then z else 0))
      (Ioi (0 : ℝ)) μ := by sorry
