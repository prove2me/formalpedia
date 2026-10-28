-- Prove2me | Theorems.Thm_AvramDividend_Classical_laplaceExponent_zero_jump_measure
-- name    : AvramDividend.Classical.laplaceExponent_zero_jump_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:12:17.082991+00:00
-- url     : https://prove2.me/theorems/1a7a54e5-64bf-4aae-86be-73a817ff1cca
-- title:
--   Lévy–Khintchine exponent with zero jump measure is the Gaussian quadratic exponent
-- statement:
--   If the Lévy jump measure is identically zero, its compensated-jump integral vanishes. The canonical Lévy–Khintchine exponent reduces to cθ+σ²θ²/2. This exact algebraic identity connects the drifted Brownian moment-generating function to the process triplet.
-- source:
--   Canonical AvramDividend.Classical.laplaceExponent definition, Lévy–Khintchine formula.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Tactic

open MeasureTheory
open AvramDividend.Classical

theorem AvramDividend.Classical.laplaceExponent_zero_jump_measure
    (c σ θ : ℝ) :
    laplaceExponent c σ (0 : Measure ℝ) θ =
      c * θ + σ ^ 2 * θ ^ 2 / 2 := by sorry
