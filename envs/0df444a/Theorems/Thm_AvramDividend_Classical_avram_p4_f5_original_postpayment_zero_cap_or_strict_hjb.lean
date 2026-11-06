-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f5_original_postpayment_zero_cap_or_strict_hjb
-- name    : AvramDividend.Classical.avram_p4_f5_original_postpayment_zero_cap_or_strict_hjb
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:23:23.756207+00:00
-- url     : https://prove2.me/theorems/252e11e4-6660-486c-a38d-3989e06eab9d
-- title:
--   Original post-rightpayment reserve partitions into zero, exact cap, or interior with genuine HJB generator and gradient signs
-- statement:
--   At every actual original-process time zero or strictly prior to ruin, the post-rightpayment reserve is either zero, exactly at the cap, or in the positive strict interior. In the interior, both the genuine original Lévy-generator inequality and the dividend slope inequality hold. This packages the correct source-domain case distinction for finite-clock Itô–Meyer without illicitly applying C2 interior estimates at cap contact or at zero.
-- source:
--   Combine the already Proved physical admissible-reserve trichotomy `f1496f35` with the canonical hw_gen and hw_grad. No artificial process, no extra assumptions and no post-ruin use.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_postpayment_reserve_zero_cap_interior_partition

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f5_original_postpayment_zero_cap_or_strict_hjb
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (0 < t ∧ (t : ℝ≥0∞) < ruinTime X x D ω)) :
    let y := x + X.X t ω - rightLimit D t ω
    y = 0 ∨ ENNReal.ofReal y = C ∨
      (0 < y ∧ ENNReal.ofReal y < C ∧
        X.GeneratorIntegrable w y ∧
        X.generator w y - q * w y ≤ 0 ∧
        1 ≤ deriv w y) := by sorry
