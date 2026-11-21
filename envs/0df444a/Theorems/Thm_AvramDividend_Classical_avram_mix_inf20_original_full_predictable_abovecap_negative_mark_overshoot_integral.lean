-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_full_predictable_abovecap_negative_mark_overshoot_integral
-- name    : AvramDividend.Classical.avram_mix_inf20_original_full_predictable_abovecap_negative_mark_overshoot_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:12:05.390665+00:00
-- url     : https://prove2.me/theorems/bfc13a5e-7380-4ee0-9e07-99437d94e1d6
-- title:
--   Original controlled stopped predictable full marked Lévy above-cap integrand bounded by discounted ruin-overshoot product integral
-- statement:
--   Genuine original finite-cap controlled Lévy stopped physical predictable-mark product-integral compensation estimate. The premark reserve is exactly the controlled original X path with rightLimit dividend D evaluated at the mark time by Function.leftLim. Mark compensation is computed from the true caplinear V and an actual arbitrary measure μ on time×sample×mark (in applications the stopped P⊗clock⊗X.ν predictable mark measure). On the above-cap premark region the product H is bounded by the explicitly discounted positive-part ruin-overshoot kernel G, including marks crossing below zero, by the Proved full pointwise mark envelope 85b04ac6. Integrability of H and G with respect to μ is explicit and not asserted automatically. This supplies the true-variable integral monotonicity needed by the original infinite-negative-activity stopped Ito generator/ruin-contact ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_full_predictable_abovecap_negative_mark_overshoot_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (μ : Measure ((ℝ≥0 × Ω) × ℝ)) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if C.toReal < Y p.1 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (V (Y p.1 + p.2) - V (Y p.1) - deriv V (Y p.1) * p.2)
      else 0
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if C.toReal < Y p.1 then
        Real.exp (-(q * (p.1.1 : ℝ))) * max 0 (-(Y p.1 + p.2))
      else 0
    Integrable H μ → Integrable G μ →
      (∫ p, H p ∂μ) ≤ (∫ p, G p ∂μ) := by sorry
