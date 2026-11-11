-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_hjb_diff_comparison
-- name    : AvramDividend.Classical.avram_mix_fin26_hjb_diff_comparison
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:29:37.244551+00:00
-- url     : https://prove2.me/theorems/4e355646-7419-4df0-a2ad-9999fc736687
-- title:
--   Original mixed Lévy HJB inequality yields a first-order upper comparison for the second derivative
-- statement:
--   Suppose the original mixed spectrally negative Lévy generator satisfies the HJB supersolution bound and its negative-jump contribution is at least -jumpRate w(y). If w(y)≤W, q+jumpRate≥0, and a=σ²/2>0, constants β and ε satisfying -c≤aβ and (q+jumpRate)W≤aε give w''(y)≤βw'(y)+ε whenever w'(y)≥0. This is the precise differential bound needed to apply the already Proved derivative ODE comparison at a finite dividend cap, avoiding an unjustified globally bounded-derivative assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin26_hjb_diff_comparison
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (q jumpRate W β ε y : ℝ)
    (hA : 0 < X.σ ^ 2 / 2)
    (hJump : -jumpRate * w y ≤
      ∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν)
    (hHJB : X.generator w y - q * w y ≤ 0)
    (hUpper : w y ≤ W) (hQLambda : 0 ≤ q + jumpRate)
    (hBeta : -X.c ≤ (X.σ ^ 2 / 2) * β)
    (hEps : (q + jumpRate) * W ≤ (X.σ ^ 2 / 2) * ε)
    (hDeriv : 0 ≤ deriv w y) :
    iteratedDeriv 2 w y ≤ β * deriv w y + ε := by sorry
