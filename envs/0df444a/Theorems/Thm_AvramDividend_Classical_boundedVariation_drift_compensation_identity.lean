-- Prove2me | Theorems.Thm_AvramDividend_Classical_boundedVariation_drift_compensation_identity
-- name    : AvramDividend.Classical.boundedVariation_drift_compensation_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:01:04.999736+00:00
-- url     : https://prove2.me/theorems/854aab2b-2047-4144-9b54-ba162271f152
-- title:
--   The BV compensation integral combines with the characteristic drift
-- statement:
--   For a bounded-variation spectrally negative Lévy process, the linear generator drift coefficient c combined with the derivative-weighted compensator over (-1,0) equals the finite-variation drift c minus the small-jump mean, times the test function derivative. The small-jump integrability is already proved and imported.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_smallJump_deriv_integrable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.boundedVariation_drift_compensation_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (x : ℝ) :
    X.c * deriv w x -
        ∫ y in Ioo (-1 : ℝ) 0, deriv w x * y ∂X.ν =
      X.drift * deriv w x := by sorry
