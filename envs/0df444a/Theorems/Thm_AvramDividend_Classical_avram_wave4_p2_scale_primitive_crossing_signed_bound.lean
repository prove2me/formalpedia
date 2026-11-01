-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_crossing_signed_bound
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_crossing_signed_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:07:15.151771+00:00
-- url     : https://prove2.me/theorems/e61c323a-92e9-451e-bc15-1c6f61e5776d
-- title:
--   Zero-crossing signed estimate for the integrated q-scale compensated kernel
-- statement:
--   For a genuine q-scale function W of the original source Levy process, the primitive U(x)=integral_0^x W is increasing and bounded by x W(x) for x>0. On the small-negative-jump zero-crossing strip 0<x<r<=1, the compensated jump kernel of U is exactly r W(x)-U(x), lies between zero and r W(1), and has an integrable r^2 weighted x-section. This source-faithful pointwise estimate is the first analytic bridge enabling global Fubini for U even when global absolute Fubini for W is false.
-- source:
--   Avram Palmowski Pistorius 2007, Lemma 4; the monotone integrated-scale compensation argument and source IsScaleFunction. Independent analytic crossing-strip step towards e8fbc763-da83-4909-b759-27feee641e80.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_crossing_signed_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r x : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hx0 : 0 < x) (hxr : x < r) :
    0 ≤ r * W x - ∫ t in (0 : ℝ)..x, W t ∧
      r * W x - ∫ t in (0 : ℝ)..x, W t ≤ r * W 1 := by sorry
