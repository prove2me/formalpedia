-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_source_C1_negative_kernel_product_L1_from_physical_band
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_full_source_C1_negative_kernel_product_L1_from_physical_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:44:43.724843+00:00
-- url     : https://prove2.me/theorems/935a3635-5968-41d2-b69a-e357d4c19856
-- title:
--   Original BV stopped C1 negative-jump product L1 with automatic physical value bound, Lipschitz and predictability
-- statement:
--   On the actual original Ω/P/filtration X and dividend D, C1 smoothness on a compact positive-cap reserve strip gives a uniform Lipschitz derivative bound, original continuity and zero-negative extension give the global below-ceiling candidate bound, and the previously Proved source kernel measurability gives the exact predictable indicator kernel. These automatically discharge all three auxiliary premises of the already-Proved source BV product L1 theorem 221ffdc4. Its remaining requirements are the physically finite predictable clock, a strict interior cap strip, the first-variation derivative constant K, and finite negative Lévy tail separated from zero; these are explicit original-process hypotheses. This gives a direct W8-04 intensity-side signed L1 input without claiming the stopped Itô identity.
-- source:
--   Source-faithful combination of Proved 47d6d44f below-ceiling |w|, Proved 82f28985 physical BV C1 compact Lipschitz, Proved d4504671 exact discounted marked predictability, and Proved 221ffdc4 original signed product L1. Publication repair: the original definitional if on a predictable event requires a classical decidability instance at statement elaboration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_02_original_BV_full_source_C1_negative_kernel_product_L1_from_physical_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBandSmooth : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc (a / 2) b, ‖deriv w y‖₊ ≤ K)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : ∀ p, H p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
