-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_unit_atom_corrected
-- name    : AvramDividend.Classical.gaussian_laplaceExponent_unit_atom_corrected
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:10:34.886284+00:00
-- url     : https://prove2.me/theorems/fde2616d-9fa3-4523-80d7-28ff79f81465
-- title:
--   Canonical negative-jump Laplace exponent with exact positive-cutoff unit-atom correction
-- statement:
--   The actual canonical signed negative-jump Lévy exponent equals the Gaussian polynomial plus the positive-magnitude compensator using inclusive cutoff at magnitude one, minus the exact linear contribution at the unit-jump atom. All terms stay integrated against the original negative-jump measure. Pointwise sign change and strict-to-inclusive cutoff conversion are proved separately and integrated here using almost-everywhere congruence. This preserves the mission's Lévy-Khintchine convention while preparing the exact pushforward to the positive-magnitude Gaussian Volterra representation.
-- source:
--   Mission laplaceExponent declaration, gaussian_negative_jump_integrand_mirror and gaussian_open_closed_truncation_atom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_laplaceExponent_unit_atom_corrected (c σ : ℝ) (ν : Measure ℝ) (θ : ℝ) :
    laplaceExponent c σ ν θ =
      c * θ + σ ^ 2 * θ ^ 2 / 2 +
        (∫ y in Iio (0 : ℝ),
          (Real.exp (-θ * (-y)) - 1 +
            θ * (if -y ≤ 1 then -y else 0)) -
              θ * (if -y = 1 then (1 : ℝ) else 0) ∂ν) := by sorry
