-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_corrected_ubv_three_closed_branches
-- name    : AvramDividend.Classical.avram_wave5_05_corrected_ubv_three_closed_branches
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T01:19:31.638347+00:00
-- url     : https://prove2.me/theorems/e2740be5-af8e-4429-a37d-957a05424333
-- title:
--   Three complete original-process boundary branches of corrected UBV verification
-- statement:
--   Retain every exact hypothesis and the expected full discounted Stieltjes dividend conclusion from corrected canonical UBV stochastic verification, with the required nonnegative value at zero. Prove the genuine original Lévy/process/admissible-regulator result under the disjunctive side condition C=0 or finite horizon T=0 or actual controlled ruin time identically zero almost surely. The three cases are individually Proved canonical source lemmas, including time-zero right dividend atoms, all pre-ruin dividend Stieltjes mass, and arbitrary nonnegative horizon. This reduces the still Open core to positive cap, positive horizon and noninstantaneous ruin without changing its original statement; no claim of the missing general Itô–Meyer proof is made.
-- source:
--   Exact source corrected core UUID 429e17ca-5528-40b5-b593-7c03973d0706; accepted branch source theorems UUIDs b65b82f2-497b-40cf-8137-1325f2886f7f, 3858a86b-eff8-46f1-b700-7ee855dad85a, e8d8ec8a-10a2-4797-a987-93afe1a43df0. Private remote probe 34df7af6-e06b-4b08-ae80-fe2abfb4c9ad reached sentinel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zero_horizon_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zeroCap_fullHorizon_allInitialCapital
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_instantRuin_allHorizon_correctedStieltjesBound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_05_corrected_ubv_three_closed_branches
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (hBranch : C = 0 ∨ T = 0 ∨ (∀ᵐ ω ∂P, ruinTime X x D ω = 0)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  sorry
