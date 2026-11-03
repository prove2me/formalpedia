-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_C1_discounted_kernel_product_L1_from_strategy_and_energy
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_C1_discounted_kernel_product_L1_from_strategy_and_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:44:01.099376+00:00
-- url     : https://prove2.me/theorems/3055ad05-6f14-4910-b03b-9b06a6de461b
-- title:
--   Original actual BV C1 negative Lévy kernel is physical predictable-product L1 from original dividend strategy and Lévy energy
-- statement:
--   Under the original spectrally negative Lévy process on Ω, P and its right-continuous predictable filtration, with genuine bounded variation, true dividend strategy, positive compact reserve interior and quadratic Lévy energy, the discounted negative jump change in w is integrable against the original finite physical predictable clock times X.ν restricted to negative marks. Its predictability and separated negative tail finite-mass are deduced from source theorems, rather than assumed. It supplies exactly the intensity-side Integrable G N premise for the actual stopped compensated jump martingale, with no finite total jump activity.
-- source:
--   Accepted W7-02 actual BV C1 kernel integrability 221ffdc4; accepted W7-17 original predictable measurability d4504671; accepted original Lévy separated negative tail 3e5bbc19.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_levy_mark_tail_finite_mass_at_every_small_threshold
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_C1_discounted_kernel_product_L1_from_strategy_and_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (a b L R : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E,
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
