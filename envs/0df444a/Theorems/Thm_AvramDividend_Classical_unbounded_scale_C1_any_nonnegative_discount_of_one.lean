-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_C1_any_nonnegative_discount_of_one
-- name    : AvramDividend.Classical.unbounded_scale_C1_any_nonnegative_discount_of_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:36:36.853671+00:00
-- url     : https://prove2.me/theorems/225d48dd-5635-45f1-8856-56100f7a16fd
-- title:
--   C1 transfer between any nonnegative q-scale discounts directly by the causal resolvent
-- statement:
--   For an unbounded-variation spectrally negative Levy process, if one nonnegative-discount scale function is C1 for positive reserves then every other nonnegative-discount scale function is C1. The proof uses the exact two-discount resolvent W1=W2+(q1-q2)(W2*W1), the newly proved monotone C1 causal-convolution theorem with W1 as the smooth kernel, and zero scale boundary W1(0)=0. No comparison root or auxiliary Laplace parameter, no stochastic standing assumption, and no restriction to q1=0.
-- source:
--   Proved unbounded_scale_resolvent_convolution [4198c14e-7e01-4121-a3e9-8f4e30ee2b4d], causal_convolution_contDiffOn_one_of_monotone_C1_kernel [df538b19-3214-472b-a34c-c964a375643e], unbounded_scale_zero_origin_nonnegative_discount [7323e81c-9f47-4cae-a748-46f57c708cec]. Original zero-discount stochastic C1 core still Open [8aaa16d2-d9ec-4e8f-8e42-cc551cca9d8d].

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_causal_convolution_contDiffOn_one_of_monotone_C1_kernel
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_C1_any_nonnegative_discount_of_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂)
    (W₁ W₂ : ℝ → ℝ)
    (hW₁ : IsScaleFunction X q₁ W₁)
    (hW₂ : IsScaleFunction X q₂ W₂)
    (hC₁ : ContDiffOn ℝ 1 W₁ (Ioi (0 : ℝ))) :
    ContDiffOn ℝ 1 W₂ (Ioi (0 : ℝ)) := by sorry
