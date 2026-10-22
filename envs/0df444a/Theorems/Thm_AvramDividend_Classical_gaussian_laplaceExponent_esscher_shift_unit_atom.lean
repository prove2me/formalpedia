-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_esscher_shift_unit_atom
-- name    : AvramDividend.Classical.gaussian_laplaceExponent_esscher_shift_unit_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:00:27.872533+00:00
-- url     : https://prove2.me/theorems/667361e8-3daf-4df0-9cd7-5fde57e2e385
-- title:
--   Exact Gaussian Esscher shift for the classical signed-jump Lévy exponent
-- statement:
--   Under the positive-magnitude Lévy truncated-square integrability condition, shifting the actual classical spectrally negative signed-jump Lévy exponent by a nonnegative amount has the exact Gaussian quadratic, tilted linear drift and positive double-tail compensator decomposition. The tilted linear drift retains the correction for possible jumps of magnitude exactly one, because the mission uses open truncation whereas the Gaussian Volterra helper uses inclusive truncation. This bridges the remotely Proved Gaussian shift identity to the model's own exponent.
-- source:
--   Proved Gaussian real Esscher-shift theorem combined with the exact signed-model inclusive cutoff and drift-atom correction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.gaussian_laplaceExponent_esscher_shift_unit_atom (c σ φ θ : ℝ) (ν : Measure ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂(ν.map (fun y : ℝ => -y))) < ⊤) :
    laplaceExponent c σ ν (φ + θ) - laplaceExponent c σ ν φ =
      θ * (c - (ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) + σ ^ 2 * φ +
        (∫ z in Ioi (0 : ℝ), (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z) ∂(ν.map (fun y : ℝ => -y)))) +
      (σ ^ 2 / 2) * θ ^ 2 +
      (∫ z in Ioi (0 : ℝ), Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z) ∂(ν.map (fun y : ℝ => -y))) := by sorry
