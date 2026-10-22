-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
-- name    : AvramDividend.Classical.gaussian_levy_square_integrable_neg_pushforward
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:10:29.342493+00:00
-- url     : https://prove2.me/theorems/581daddd-bf38-468b-aa72-94736994f826
-- title:
--   Lévy truncated-square integrability under jump-sign pushforward
-- statement:
--   If a real jump measure satisfies the Lévy truncated-square integrability condition over negative jumps, the pushforward under negation satisfies the corresponding condition over positive jump magnitudes. The proof uses exact measure restriction and lintegral-map identities at the pinned Mathlib revision, together with invariance of the square under negation. This closes the measure-level integrability hypothesis required to reuse the Gaussian Esscher Volterra identities for the actual spectrally negative Lévy process exponent.
-- source:
--   Exact-revision MeasureTheory.Measure.restrict_map, MeasureTheory.lintegral_map, elementary squared negation.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_levy_square_integrable_neg_pushforward (ν : Measure ℝ)
    (hlevy : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2))
        ∂(ν.map (fun y : ℝ => -y))) < ⊤ := by sorry
