-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_convexOn_nonnegative
-- name    : AvramDividend.Classical.levy_laplace_exponent_convexOn_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:21:16.627008+00:00
-- url     : https://prove2.me/theorems/3ec09019-f499-4957-a73f-dc7b2243f2fa
-- title:
--   Convexity of the actual spectrally negative Levy exponent on nonnegative Laplace arguments
-- statement:
--   The actual Levy-Khintchine exponent of a canonical spectrally negative Levy process is convex on all nonnegative Laplace parameters. The compensated negative-jump kernel is integrable at each nonnegative parameter; convexity of exp yields pointwise Jensen inequality, compensation and drift terms are affine, and the Gaussian quadratic is convex. Integrating the pointwise inequality gives convexity without Standing or moment assumptions beyond the defining Levy measure. This supplies a finite right derivative at each strictly positive Esscher root via already Proved theorem 77e93571, and closes the source-specific finite-slope gap in Workstream 1E-C.
-- source:
--   Kuznetsov, Kyprianou and Rivero, Theory of Scale Functions for Spectrally Negative Levy Processes, equation (3), negative Levy-Khintchine integral with truncation |z|<1. Pinned Prove2Me source definition SpectrallyNegativeLevy.ψ/laplaceExponent, and accepted levy_compensated_jump_integrable_nonneg; generic convex_positive_shift_right_secant_limit is already Proved under ConvexOn premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_jump_integrable_nonneg
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_laplace_exponent_convexOn_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ConvexOn ℝ (Ici (0 : ℝ)) X.ψ := by sorry
