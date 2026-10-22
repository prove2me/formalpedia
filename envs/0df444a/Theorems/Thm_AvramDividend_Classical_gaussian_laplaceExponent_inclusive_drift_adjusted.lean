-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_inclusive_drift_adjusted
-- name    : AvramDividend.Classical.gaussian_laplaceExponent_inclusive_drift_adjusted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T11:54:16.729988+00:00
-- url     : https://prove2.me/theorems/ded02d71-82ac-42ba-b826-2c9ef091f3a3
-- title:
--   Exact unit-atom drift correction for the signed Lévy exponent
-- statement:
--   For nonnegative Laplace argument and a negative-jump Lévy measure whose sign-reflected positive magnitude pushforward obeys the Lévy truncated-square integrability condition, the model's strictly truncated Lévy–Khintchine exponent equals the inclusive cutoff Gaussian exponent with drift reduced by exactly the finite unit-atom mass. The correction permits rigorous use of the previously Proved Gaussian Esscher and Volterra identities without dropping possible jumps of exactly unit magnitude.
-- source:
--   Pinned Bochner integral_sub; Gaussian positive-magnitude exponent bridge, unit-atom integrability and exact unit-atom integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.gaussian_laplaceExponent_inclusive_drift_adjusted (c σ θ : ℝ) (ν : Measure ℝ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂(ν.map (fun y : ℝ => -y))) < ⊤) :
    laplaceExponent c σ ν θ =
      (c - (ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ)) * θ +
        σ ^ 2 * θ ^ 2 / 2 +
        (∫ z in Ioi (0 : ℝ), Real.exp (-θ * z) - 1 +
          θ * (if z ≤ 1 then z else 0) ∂(ν.map (fun y : ℝ => -y))) := by sorry
