-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_horizon_discounted_compact_value_predictable_L2
-- name    : AvramDividend.Classical.avram_wave7_18_original_horizon_discounted_compact_value_predictable_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:43:27.219416+00:00
-- url     : https://prove2.me/theorems/2af60ecc-a8d1-4714-8837-f3430094e182
-- title:
--   Exact original-filtration positive-C2 compact reserve value has finite discounted predictable energy
-- statement:
--   For the genuine original SpectrallyNegativeLevy process X, admissible dividend control D and strictly left-limit postpayment reserve Y, assume w is twice continuously differentiable on the exact positive interior {y | 0<y and ENNReal.ofReal y<C}. Mask w(Y) on a compact interval [u,v] contained in a strict positive interior interval (a,b). Multiply by the finite-horizon nonnegative-q discount factor 1_{t<=T} exp(-qt). Then the resulting original right-continuous-filtration predictable integrand is measurable and has finite square energy against every finite predictable measure. The statement covers C=top and preserves the strict-left and right-dividend-jump convention. It neither asserts global Levy compensator integrability nor any ruin-clock identity.

import Mathlib
import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_predictable_value_compact_L2_from_C2_domain
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_horizon_discounted_compact_value_predictable_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b u v : ℝ)
    (ha : 0 < a) (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hband : ∀ y : ℝ, y ∈ Ioo a b → ENNReal.ofReal y < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let V : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then w (Y p) else 0
    let weight : ℝ≥0 × Ω → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let J : ℝ≥0 × Ω → ℝ := fun p => weight p * V p
    Measurable[𝓕.rightCont.predictable] J ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((J p) ^ 2) ∂μ) < ⊤ := by sorry
