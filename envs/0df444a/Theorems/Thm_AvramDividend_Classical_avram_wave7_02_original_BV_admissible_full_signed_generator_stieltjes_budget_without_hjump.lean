-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_admissible_full_signed_generator_stieltjes_budget_without_hjump
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_admissible_full_signed_generator_stieltjes_budget_without_hjump
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:25:00.964819+00:00
-- url     : https://prove2.me/theorems/d37cea6d-cf10-429b-b592-26bfc14e4065
-- title:
--   Original BV signed physical-generator and full Stieltjes local HJB bound from admissibility without a separate dividend jump hypothesis
-- statement:
--   The complete original-source BV local signed HJB budget, consisting of the actual time-zero right Stieltjes atom, the predictable Lévy-generator integral and the real diffuse/singular-continuous dividend-measure derivative integral, holds under the original capped admissibility and C1 candidate assumptions with no separate hjump premise. The previous Proved integral theorem is applied with hjump derived from exact original reserve and dividend definitions. The assumptions on measurable localised sets, their interior region and integrability remain explicit. No stochastic compensation or passage to the ruin/horizon limit is claimed.
-- source:
--   Compose Proved original physical-generator/Stieltjes HJB signed budget 0414350e with proved canonical C1/admissibility hjump 5b71b5ce, preserving X, Ω, predictability and original Stieltjes measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_initial_atom_and_local_physical_generator_full_stieltjes_HJB_budget
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_admissible_full_signed_generator_stieltjes_budget_without_hjump
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
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
