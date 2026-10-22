-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_levy_positive_restrict_sigmaFinite
-- name    : AvramDividend.Classical.gaussian_levy_positive_restrict_sigmaFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:13:51.40658+00:00
-- url     : https://prove2.me/theorems/9d1e3ef1-dc9a-4db6-93c6-7bfcf3c5551f
-- title:
--   Sigma-finite positive restriction of a truncated-square Lévy measure
-- statement:
--   A positive-side Lévy measure with finite truncated-square integral has a sigma-finite restriction to (0,infinity). One uses the finite-mass reciprocal tails together with a null nonpositive half-line and a countable covering family.
-- source:
--   Finite positive Lévy tails, Archimedean reciprocal covering, and Mathlib sigmaFinite_iff.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_levy_positive_restrict_sigmaFinite
    (μ : Measure ℝ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    SigmaFinite (μ.restrict (Ioi (0 : ℝ))) := by sorry
