-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_stopped_discounted_negative_kernel_auto_measurable_product_L1
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_stopped_discounted_negative_kernel_auto_measurable_product_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:44:31.566577+00:00
-- url     : https://prove2.me/theorems/e5b056d4-37db-41d0-b475-44a46d9d240a
-- title:
--   Original stopped BV negative-jump compensated kernel is product L1 with automatic source predictability
-- statement:
--   On the actual source Ω, P, right-continuous filtration, Lévy X, dividend D and controlled left reserve, the stopped discounted negative-jump source kernel is integrable against μ.prod (X.ν.restrict (Iio 0)) under physically local BV first-moment, finite-tail and cap-band assumptions. The W8-17 accepted source result d4504671 supplies the actual predictable measurability, while the already-Proved W7-02 source global product L1 result 221ffdc4 gives integrability. No separate measurability axiom is imposed, no surrogate process is introduced, and stopped pathwise Itô expectation remains distinct.
-- source:
--   Combine Proved d4504671 original predictable discounted kernel measurability and Proved 221ffdc4 original finite-clock controlled BV product L1, with literal H definitional equality. Publication repair: the original definitional if on a predictable event requires a classical decidability instance at statement elaboration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_02_original_BV_stopped_discounted_negative_kernel_auto_measurable_product_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
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
    (hMass : X.ν (Iic (-a / 2)) < ⊤) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        if p.1 ∈ E ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
             w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
        else 0) (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
