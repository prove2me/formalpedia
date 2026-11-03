-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:01:20.485103+00:00
-- url     : https://prove2.me/theorems/221ffdc4-c079-4b20-ab43-05722d569691
-- title:
--   Original BV stopped controlled C1 nonlinear source jump kernel is genuinely L1 on finite right-continuous predictable Levy product clock
-- statement:
--   For the actual original spectrally negative bounded-variation Levy source on its unchanged right-continuous predictable filtration, and the real controlled left reserve localised to a compact positive strip, the complete discounted nonlinear negative-source-jump kernel H(p,z) supported on the stopped interior E has genuine L1 integrability under a finite physical predictable clock μ times the original X.ν. The proof combines exact small first-variation plus finite large-tail BV Levy mark envelope, the actual source C1 pointwise bound including ruin overshoot marks, and genuine marked product-measure L1 domination. Only strong measurability of H and physical tail mass remain explicit; no C2, copied Poisson source or compensation identity is assumed.
-- source:
--   W7-02 three new original-source proved interfaces: full physical piecewise mark envelope, actual discounted controlled jump pointwise domination, predictable marked product L1 domination.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_negative_levy_small_first_moment_large_finite_piecewise_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_full_negative_source_mark_discounted_piecewise_variation_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_predictable_mark_kernel_L1_from_physical_mark_envelope
open MeasureTheory Set Filter
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (hq : 0 ≤ q) (a b L R : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (E : Set (ℝ≥0 × Ω))
    (hEregion : ∀ p ∈ E,
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : ∀ p, H p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0)
    (hHm : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      AEStronglyMeasurable H (μ.prod (X.ν.restrict (Iio (0 : ℝ)))))) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
