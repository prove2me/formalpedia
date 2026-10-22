-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite
-- name    : AvramDividend.Classical.gaussian_negative_jump_pushforward_sigmaFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:35:03.953376+00:00
-- url     : https://prove2.me/theorems/08bca239-504e-44c2-b776-0a820110e9f6
-- title:
--   Sigma-finite positive-magnitude pushforward of a negative Lévy jump measure
-- statement:
--   If a negative-side Lévy jump measure has no nonnegative mass and satisfies the negative truncated-square Lévy condition, its negation pushforward onto positive magnitudes is sigma-finite. This follows from accepted support and integrability pushforward bridges plus positive-supported sigma-finiteness.
-- source:
--   Proved gaussian_negative_jump_pushforward_support, gaussian_levy_square_integrable_neg_pushforward, and positive-supported Lévy sigma-finiteness.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_negative_jump_pushforward_sigmaFinite
    (ν : Measure ℝ)
    (hν : ν (Ici (0 : ℝ)) = 0)
    (hlevy : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    SigmaFinite (ν.map (fun y : ℝ => -y)) := by sorry
