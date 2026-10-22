-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_laplaceExponent_pushforward_unit_atom
-- name    : AvramDividend.Classical.gaussian_laplaceExponent_pushforward_unit_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:10:50.297665+00:00
-- url     : https://prove2.me/theorems/797c0937-8468-413a-a9e7-ec74c79917e2
-- title:
--   Canonical Lévy exponent with inclusive positive cutoff and exact unit-atom correction
-- statement:
--   The actual Avram spectrally negative Lévy exponent equals the positive jump-magnitude Gaussian Lévy–Khintchine integral with inclusive cutoff z≤1 minus the exact linear contribution supported on the boundary atom z=1, all integrated against the negation pushforward measure. This theorem reconciles the different truncation conventions without discarding atoms and connects the actual mission exponent to the canonical cutoff used in the Prove2Me-accepted Gaussian Volterra theorems.
-- source:
--   gaussian_laplaceExponent_positive_magnitude and gaussian_open_closed_truncation_atom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_laplaceExponent_pushforward_unit_atom (c σ θ : ℝ) (ν : Measure ℝ) :
    laplaceExponent c σ ν θ =
      c * θ + σ ^ 2 * θ ^ 2 / 2 +
        (∫ z in Ioi (0 : ℝ),
          (Real.exp (-θ * z) - 1 +
            θ * (if z ≤ 1 then z else 0)) -
              θ * (if z = 1 then (1 : ℝ) else 0)
              ∂(ν.map (fun y : ℝ => -y))) := by sorry
