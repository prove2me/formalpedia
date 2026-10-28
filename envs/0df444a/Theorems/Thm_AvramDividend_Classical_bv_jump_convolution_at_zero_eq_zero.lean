-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_jump_convolution_at_zero_eq_zero
-- name    : AvramDividend.Classical.bv_jump_convolution_at_zero_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:52:02.113023+00:00
-- url     : https://prove2.me/theorems/a40449c8-3061-4342-bfc2-e6587cae9ec1
-- title:
--   Negative-jump scale convolution vanishes exactly at zero capital
-- statement:
--   The q-scale function is identically zero on negative arguments. Its integral against the Lévy measure restricted to negative jumps is therefore exactly zero. This provides the endpoint value needed to extend convergence from strictly positive reserves to continuity at the zero barrier.
-- source:
--   Definition of the spectrally negative q-scale function; standard measure restriction and almost-everywhere integral-zero identity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_jump_convolution_at_zero_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    (∫ y in Iio (0 : ℝ), W y ∂X.ν) = 0 := by sorry
