-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_crossing_weighted_quadratic_strip
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_crossing_weighted_quadratic_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:23:24.315353+00:00
-- url     : https://prove2.me/theorems/8516e7bf-edd7-46f0-ae26-77aee94bf1b1
-- title:
--   Exponentially weighted source primitive crossing strip retains quadratic small-jump mass
-- statement:
--   For every real original source q-scale function, compensated primitive crossing mass on 0<x<r≤1 remains integrable after multiplying by exp(-θx), θ≥0, and its integral is bounded by the same source O(r²) term W(1)r². This upgrades the canonically Proved unweighted source strip theorem 5becd970 via the exact inequality 0<exp(-θx)≤1 on x>0, and is the crossing half of the full source jump-product Fubini estimate together with P2 interior c0fb07f0.
-- source:
--   Avram Palmowski Pistorius 2007, Lemma 4; Proved source strip 5becd970, Mathlib Integrable.mono and setIntegral_mono_on.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_crossing_weighted_quadratic_strip
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r θ : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) (hθ : 0 ≤ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) *
        |r * W x - ∫ t in (0 : ℝ)..x, W t|)
      (Ioo (0 : ℝ) r) volume ∧
    (∫ x in Ioo (0 : ℝ) r,
      Real.exp (-(θ*x)) *
        |r * W x - ∫ t in (0 : ℝ)..x, W t|) ≤
      W 1 * r^2 := by sorry
