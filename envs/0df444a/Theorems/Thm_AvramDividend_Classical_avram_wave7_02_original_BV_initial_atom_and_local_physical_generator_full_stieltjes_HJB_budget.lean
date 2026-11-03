-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_atom_and_local_physical_generator_full_stieltjes_HJB_budget
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_initial_atom_and_local_physical_generator_full_stieltjes_HJB_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:10:08.173837+00:00
-- url     : https://prove2.me/theorems/0414350e-c565-456e-b575-432c10358e85
-- title:
--   Original BV complete time-zero right Stieltjes mass plus physical predictable generator and singular-dividend HJB signed budget
-- statement:
--   Within the original BV spectrally negative Levy filtration, the exact physical local HJB generator contributes a nonpositive predictable-space-time integral, the genuine complete singular/diffuse original dividendMeasure contributes a nonpositive discounted gradient correction, and the full right Stieltjes atom at time zero is bounded by the initial candidate. Under explicit integrability and interior localisation, the complete signed combination is bounded by w(x). No realised-source Ito equality or outside-interior limit is presumed.
-- source:
--   Proved original actual timezero dividend Stieltjes HJB singleton 0315346e, original signed Stieltjes gradient f2c20057, original physical generator supersolution and integrable predictable clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_stieltjes_dividend_interior_gradient_nonpositive
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_initial_atom_and_local_physical_generator_full_stieltjes_HJB_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E,
      0 < Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (F : (ℝ≥0 × Ω) → ℝ)
    (hF : ∀ p ∈ E, F p =
      Real.exp (-(q * (p.1 : ℝ))) *
      (X.generator w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1)))
    (hFI : IntegrableOn F E μ)
    (A : Set ℝ) (hAm : MeasurableSet A)
    (hAregion : ∀ t ∈ A,
      0 < riskProcess X x D t.toNNReal ω ∧
      ENNReal.ofReal (riskProcess X x D t.toNNReal ω) < C)
    (hIDiv : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω)))
      A (dividendMeasure D ω)) :
    (w (x - rightLimit D 0 ω) + rightLimit D 0 ω) +
      (∫ p in E, F p ∂μ) +
      (∫ t in A, Real.exp (-(q * t)) *
        (1 - deriv w (riskProcess X x D t.toNNReal ω))
        ∂(dividendMeasure D ω)) ≤ w x := by sorry
